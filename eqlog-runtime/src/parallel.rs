//! Concurrent evaluation of independent tasks while closing a model.
//!
//! Each task writes only state that it owns, such as one trie or the output
//! buffers of one rule module, and the caller consumes outputs in a fixed
//! order afterwards. Results thus do not depend on how tasks are scheduled.

use std::any::Any;
use std::collections::VecDeque;
use std::io;
use std::panic::{self, AssertUnwindSafe};
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::thread;

/// Work that reads shared state and writes only state that it owns.
pub type Task<'a> = Box<dyn FnOnce() + Send + 'a>;

type Job = Box<dyn FnOnce() + Send + 'static>;

// Below this many new rows, waking workers costs more than it saves.
const PARALLEL_WORK: usize = 64;
// Rule evaluation of the large developments we measured stops scaling here.
const MAX_THREADS: usize = 8;

struct Queue {
    jobs: Mutex<VecDeque<Job>>,
    available: Condvar,
}

impl Queue {
    fn pop(&self) -> Option<Job> {
        self.jobs.lock().unwrap().pop_front()
    }
}

struct Pool {
    queue: Arc<Queue>,
    workers: usize,
}

static POOL: OnceLock<Pool> = OnceLock::new();

fn threads() -> usize {
    match std::env::var("EQLOG_THREADS") {
        Ok(threads) => threads
            .parse()
            .expect("EQLOG_THREADS must be a number of threads"),
        Err(std::env::VarError::NotPresent) => match thread::available_parallelism() {
            Ok(threads) => threads.get().min(MAX_THREADS),
            Err(error) if error.kind() == io::ErrorKind::Unsupported => 1,
            Err(error) => panic!("querying the available parallelism failed: {error}"),
        },
        Err(std::env::VarError::NotUnicode(_)) => panic!("EQLOG_THREADS must be unicode"),
    }
}

fn pool() -> &'static Pool {
    POOL.get_or_init(|| {
        let queue = Arc::new(Queue {
            jobs: Mutex::new(VecDeque::new()),
            available: Condvar::new(),
        });
        // The thread running the tasks takes part, too.
        let workers = threads().saturating_sub(1);
        for _ in 0..workers {
            let queue = queue.clone();
            thread::Builder::new()
                .name("eqlog-worker".to_owned())
                .spawn(move || loop {
                    let job = {
                        let mut jobs = queue.jobs.lock().unwrap();
                        loop {
                            if let Some(job) = jobs.pop_front() {
                                break job;
                            }
                            jobs = queue.available.wait(jobs).unwrap();
                        }
                    };
                    job();
                })
                .expect("spawning an eqlog worker thread");
        }
        Pool { queue, workers }
    })
}

// Counts the unfinished jobs of one call and keeps the first panic.
struct Latch {
    state: Mutex<(usize, Option<Box<dyn Any + Send>>)>,
    done: Condvar,
}

/// Runs tasks to completion, in parallel when `work` new rows justify it.
///
/// A panic of a task is resumed once no other task of the call runs anymore.
pub fn run_tasks(work: usize, tasks: Vec<Task<'_>>) {
    if work < PARALLEL_WORK || tasks.len() < 2 || pool().workers == 0 {
        for task in tasks {
            task();
        }
        return;
    }
    let pool = pool();
    let latch = Arc::new(Latch {
        state: Mutex::new((tasks.len(), None)),
        done: Condvar::new(),
    });
    {
        let mut jobs = pool.queue.jobs.lock().unwrap();
        for task in tasks {
            let latch = latch.clone();
            let job: Task<'_> = Box::new(move || {
                let result = panic::catch_unwind(AssertUnwindSafe(task));
                let mut state = latch.state.lock().unwrap();
                state.0 -= 1;
                match result {
                    Ok(()) => {}
                    // Dropping a payload could panic again, so later ones leak.
                    Err(payload) => match state.1 {
                        None => state.1 = Some(payload),
                        Some(_) => std::mem::forget(payload),
                    },
                }
                if state.0 == 0 {
                    latch.done.notify_all();
                }
            });
            // SAFETY: Jobs never unwind, and this function returns only once
            // the latch has counted every job as finished, so everything the
            // tasks borrow outlives them.
            let job = unsafe { std::mem::transmute::<Task<'_>, Job>(job) };
            jobs.push_back(job);
        }
    }
    pool.queue.available.notify_all();
    while let Some(job) = pool.queue.pop() {
        job();
    }
    let mut state = latch.state.lock().unwrap();
    while state.0 > 0 {
        state = latch.done.wait(state).unwrap();
    }
    if let Some(payload) = state.1.take() {
        drop(state);
        panic::resume_unwind(payload);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn tasks_fill_their_own_outputs() {
        let mut outputs = vec![0; 100];
        let tasks = outputs
            .iter_mut()
            .enumerate()
            .map(|(i, output)| Box::new(move || *output = i * i) as Task<'_>)
            .collect();
        run_tasks(PARALLEL_WORK, tasks);
        assert!(outputs
            .iter()
            .enumerate()
            .all(|(i, &output)| output == i * i));
    }

    #[test]
    fn panics_resume_once_no_other_task_runs() {
        let started = AtomicUsize::new(0);
        let finished = AtomicUsize::new(0);
        let tasks = (0..16)
            .map(|i| {
                let (started, finished) = (&started, &finished);
                Box::new(move || {
                    started.fetch_add(1, Ordering::SeqCst);
                    if i == 3 {
                        panic!("task 3 fails");
                    }
                    finished.fetch_add(1, Ordering::SeqCst);
                }) as Task<'_>
            })
            .collect();
        let result = panic::catch_unwind(AssertUnwindSafe(|| run_tasks(PARALLEL_WORK, tasks)));
        assert!(result.is_err());
        // Only the failing task may have started without finishing.
        assert_eq!(
            started.load(Ordering::SeqCst),
            finished.load(Ordering::SeqCst) + 1
        );
    }
}
