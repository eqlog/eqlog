function asdf(): void {
  return -10;
}

function xyz(): number {
  asdf('abc', function(): void {}, 123);
}
