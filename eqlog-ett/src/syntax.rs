use std::fmt;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Location {
    pub offset: usize,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub struct Error {
    pub(crate) message: String,
    pub(crate) location: Option<Location>,
}

impl Error {
    pub(crate) fn new(message: String) -> Self {
        Self {
            message,
            location: None,
        }
    }

    pub(crate) fn at(mut self, location: Location) -> Self {
        if self.location.is_none() {
            self.location = Some(location);
        }
        self
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(location) = self.location {
            write!(f, "line {}: ", location.line)?;
        }
        self.message.fmt(f)
    }
}

impl std::error::Error for Error {}

#[derive(Clone, Debug)]
pub(crate) struct Expr {
    pub kind: ExprKind,
    pub location: Location,
    pub end: Location,
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Eq for Expr {}

impl Expr {
    pub fn relocated(&self, location: Location) -> Self {
        let mut result = self.clone();
        result.set_location(location);
        result
    }

    fn set_location(&mut self, location: Location) {
        self.location = location;
        self.end = location;
        match &mut self.kind {
            ExprKind::Name(_, args) => {
                for argument in args {
                    argument.set_location(location);
                }
            }
            ExprKind::Equal(lhs, rhs) => {
                lhs.set_location(location);
                rhs.set_location(location);
            }
            ExprKind::Refl => {}
            ExprKind::Rec {
                arguments,
                binders,
                motive,
                cases,
            } => {
                for argument in arguments {
                    argument.set_location(location);
                }
                for (_, annotation) in binders {
                    annotation.set_location(location);
                }
                motive.set_location(location);
                for case in cases {
                    case.location = location;
                    case.body.set_location(location);
                }
            }
            ExprKind::Let(_, annotation, value, body) => {
                annotation.set_location(location);
                value.set_location(location);
                body.set_location(location);
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ExprKind {
    Name(String, Vec<Expr>),
    Equal(Box<Expr>, Box<Expr>),
    Refl,
    Rec {
        arguments: Vec<Expr>,
        binders: Vec<(String, Expr)>,
        motive: Box<Expr>,
        cases: Vec<Case>,
    },
    Let(String, Box<Expr>, Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug)]
pub(crate) struct Case {
    pub location: Location,
    pub constructor: String,
    pub variables: Vec<String>,
    pub body: Expr,
}

impl PartialEq for Case {
    fn eq(&self, other: &Self) -> bool {
        self.constructor == other.constructor
            && self.variables == other.variables
            && self.body == other.body
    }
}

impl Eq for Case {}

#[derive(Debug)]
pub(crate) enum Declaration {
    Data {
        location: Location,
        name: String,
        parameters: Vec<(String, Expr)>,
        indices: Vec<(String, Expr)>,
        constructors: Vec<ConstructorDecl>,
    },
    Definition {
        location: Location,
        name: String,
        parameters: Vec<(String, Expr)>,
        result: Expr,
        body: Expr,
    },
}

#[derive(Debug)]
pub(crate) struct ConstructorDecl {
    pub location: Location,
    pub end: Location,
    pub name: String,
    pub fields: Vec<(String, Expr)>,
    pub result: Option<Expr>,
}

struct Token {
    text: String,
    location: Location,
}

pub(crate) struct Parsed {
    pub declarations: Vec<Declaration>,
    pub error: Option<Error>,
}

pub(crate) fn parse(source: &str) -> Parsed {
    let mut tokens = Vec::new();
    let mut chars = source.char_indices().peekable();
    let mut line = 1;
    let mut lexical_error = None;
    while let Some((offset, c)) = chars.next() {
        if c == '\n' {
            line += 1;
            continue;
        }
        if c.is_whitespace() {
            continue;
        }
        if c == '-' && chars.peek().map(|(_, c)| *c) == Some('-') {
            for (_, c) in chars.by_ref() {
                if c == '\n' {
                    line += 1;
                    break;
                }
            }
            continue;
        }
        let location = Location { offset, line };
        let mut text = c.to_string();
        if c.is_ascii_alphabetic() || c == '_' {
            while let Some(&(_, c)) = chars.peek() {
                if !c.is_ascii_alphanumeric() && c != '_' && c != '.' && c != '\'' {
                    break;
                }
                text.push(c);
                chars.next();
            }
        } else if (c == ':' && chars.peek().map(|(_, c)| *c) == Some('='))
            || (c == '=' && chars.peek().map(|(_, c)| *c) == Some('>'))
            || (c == '-' && chars.peek().map(|(_, c)| *c) == Some('>'))
        {
            text.push(chars.next().unwrap().1);
        } else if !"():;|=,".contains(c) {
            lexical_error = Some(Error::new(format!("unsupported character {c:?}")).at(location));
            break;
        }
        tokens.push(Token { text, location });
    }
    let mut parser = Parser { tokens, at: 0 };
    let mut declarations = Vec::new();
    while parser.peek().is_some() {
        match parser.declaration() {
            Ok(declaration) => declarations.push(declaration),
            Err(error) => {
                return Parsed {
                    declarations,
                    error: Some(error),
                }
            }
        }
    }
    Parsed {
        declarations,
        error: lexical_error,
    }
}

struct Parser {
    tokens: Vec<Token>,
    at: usize,
}

impl Parser {
    fn peek(&self) -> Option<&str> {
        self.tokens.get(self.at).map(|t| t.text.as_str())
    }

    fn location(&self) -> Location {
        self.tokens
            .get(self.at)
            .or_else(|| self.tokens.last())
            .map(|token| token.location)
            .unwrap_or_default()
    }

    fn last_location(&self) -> Location {
        self.tokens
            .get(self.at.saturating_sub(1))
            .map(|token| token.location)
            .unwrap_or_default()
    }

    fn error(&self, message: &str) -> Error {
        Error::new(message.to_owned()).at(self.location())
    }

    fn eat(&mut self, token: &str) -> bool {
        if self.peek() == Some(token) {
            self.at += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, token: &str) -> Result<(), Error> {
        if self.eat(token) {
            Ok(())
        } else {
            Err(self.error(&format!("expected {token:?}")))
        }
    }

    fn name(&mut self) -> Result<String, Error> {
        let token = self.peek().ok_or_else(|| self.error("expected a name"))?;
        if !is_name(token) {
            return Err(self.error("expected a name"));
        }
        let result = token.to_owned();
        self.at += 1;
        Ok(result)
    }

    fn declaration(&mut self) -> Result<Declaration, Error> {
        let location = self.location();
        if self.eat("inductive") {
            let name = self.name()?;
            let parameters = self.binders()?;
            let mut indices = Vec::new();
            if self.eat(":") {
                while self.peek() == Some("(") {
                    indices.extend(self.binders()?);
                    self.expect("->")?;
                }
                self.expect("Type")?;
            }
            self.expect("where")?;
            let mut constructors = Vec::new();
            while self.eat("|") {
                let constructor_location = self.location();
                let constructor = self.name()?;
                let fields = self.binders()?;
                let result = if self.eat(":") {
                    Some(self.expression()?)
                } else {
                    None
                };
                constructors.push(ConstructorDecl {
                    location: constructor_location,
                    end: self.last_location(),
                    name: constructor,
                    fields,
                    result,
                });
            }
            return Ok(Declaration::Data {
                location,
                name,
                parameters,
                indices,
                constructors,
            });
        }
        if !self.eat("def") && !self.eat("theorem") {
            return Err(self.error("expected inductive, def or theorem"));
        }
        let name = self.name()?;
        let parameters = self.binders()?;
        self.expect(":")?;
        let result = self.expression()?;
        self.expect(":=")?;
        let body = self.expression()?;
        Ok(Declaration::Definition {
            location,
            name,
            parameters,
            result,
            body,
        })
    }

    fn binders(&mut self) -> Result<Vec<(String, Expr)>, Error> {
        let mut parameters = Vec::new();
        while self.eat("(") {
            let mut names = vec![self.name()?];
            while self.peek() != Some(":") {
                names.push(self.name()?);
            }
            self.expect(":")?;
            let ty = self.expression()?;
            self.expect(")")?;
            parameters.extend(names.into_iter().map(|n| (n, ty.clone())));
        }
        Ok(parameters)
    }

    fn expression(&mut self) -> Result<Expr, Error> {
        let location = self.location();
        if self.eat("let") {
            let name = self.name()?;
            self.expect(":")?;
            let ty = self.expression()?;
            self.expect(":=")?;
            let value = self.expression()?;
            self.expect(";")?;
            let body = self.expression()?;
            return Ok(Expr {
                kind: ExprKind::Let(name, Box::new(ty), Box::new(value), Box::new(body)),
                location,
                end: self.last_location(),
            });
        }
        self.eat("by");
        self.eat("exact");
        let lhs = self.application()?;
        if self.eat("=") {
            let rhs = self.application()?;
            Ok(Expr {
                kind: ExprKind::Equal(Box::new(lhs), Box::new(rhs)),
                location,
                end: self.last_location(),
            })
        } else {
            Ok(lhs)
        }
    }

    fn application(&mut self) -> Result<Expr, Error> {
        let head = self.atom()?;
        let mut args = Vec::new();
        while self
            .peek()
            .map(|t| t == "(" || t == "rfl" || is_name(t))
            .unwrap_or(false)
        {
            args.push(self.atom()?);
        }
        if args.is_empty() {
            return Ok(head);
        }
        let location = head.location;
        match head.kind {
            ExprKind::Name(name, mut previous) => {
                previous.extend(args);
                Ok(Expr {
                    kind: ExprKind::Name(name, previous),
                    location,
                    end: self.last_location(),
                })
            }
            ExprKind::Equal(_, _)
            | ExprKind::Refl
            | ExprKind::Rec { .. }
            | ExprKind::Let(_, _, _, _) => {
                Err(self.error("only named contextual terms can be applied"))
            }
        }
    }

    fn atom(&mut self) -> Result<Expr, Error> {
        let location = self.location();
        if self.eat("(") {
            let result = self.expression()?;
            self.expect(")")?;
            return Ok(result);
        }
        if self.eat("rfl") {
            return Ok(Expr {
                kind: ExprKind::Refl,
                location,
                end: self.last_location(),
            });
        }
        if self.eat("rec") {
            let mut arguments = vec![self.application()?];
            while self.eat(",") {
                arguments.push(self.application()?);
            }
            self.expect("motive")?;
            let binders = self.binders()?;
            if binders.is_empty() {
                return Err(self.error("a motive needs a scrutinee binder"));
            }
            self.expect("=>")?;
            let motive = self.expression()?;
            self.expect("with")?;
            let mut cases = Vec::new();
            while self.eat("|") {
                let constructor_location = self.location();
                let constructor = self.name()?;
                let mut variables = Vec::new();
                while self.peek() != Some("=>") {
                    variables.push(self.name()?);
                }
                self.expect("=>")?;
                let body = self.expression()?;
                cases.push(Case {
                    location: constructor_location,
                    constructor,
                    variables,
                    body,
                });
            }
            self.expect("end")?;
            return Ok(Expr {
                kind: ExprKind::Rec {
                    arguments,
                    binders,
                    motive: Box::new(motive),
                    cases,
                },
                location,
                end: self.last_location(),
            });
        }
        Ok(Expr {
            kind: ExprKind::Name(self.name()?, Vec::new()),
            location,
            end: self.last_location(),
        })
    }
}

fn is_name(text: &str) -> bool {
    let reserved = [
        "inductive",
        "where",
        "def",
        "theorem",
        "let",
        "by",
        "exact",
        "rec",
        "motive",
        "with",
        "end",
        "rfl",
    ];
    text.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') && !reserved.contains(&text)
}
