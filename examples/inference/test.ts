let k = 5;

function asdf() {
  if (true) { 
    return 'xyz';
  } else {
    return 'abc';
  }
}

function void_func() {
  let asdffff = 5;
  while (true) {
    let fkljskljdslk = 'asd';
  }
}

function id_number(x) {
  if (true) {
    return x;
  } else {
    return k;
  }
}

function id(y) {
  return y;
}

function id2(z) {
  return id2(id)(z);
}

function id3(u) {
  if (true) {
    return u;
  } else {
    return id3(id3)(u);
  }
}

id2(5);
id2('xyz');
