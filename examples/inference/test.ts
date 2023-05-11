let k = 5;

function asdf() {
  if (true) { 
    return 'xyz';
  } else {
    return 'abc';
  }
}

function void_func() {
  let asdf = 5;
}

function id(x) {
  if (true) {
    return x;
  } else {
    return x;
  }
}

id(function () { return 5; });
