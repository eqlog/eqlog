enum Ctx {
    Empty(),
    Extended(Box<Ctx>, Ty),
}

enum Mor {
    Id(Box<Ctx>),
    Comp(Box<Mor>, Box<Mor>),
}
