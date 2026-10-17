use std::fmt;

#[derive(Clone, Debug)]
pub struct Error(pub String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl std::error::Error for Error {}

#[derive(Clone, Debug)]
pub(crate) enum Expr {
    Name(String, Vec<Expr>),
    Equal(Box<Expr>, Box<Expr>),
    Refl,
    Rec {
        scrutinee: Box<Expr>,
        variable: String,
        data: String,
        motive: Box<Expr>,
        cases: Vec<Case>,
    },
    Let(String, Box<Expr>, Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug)]
pub(crate) struct Case {
    pub constructor: String,
    pub variables: Vec<String>,
    pub body: Expr,
}

#[derive(Debug)]
pub(crate) enum Declaration {
    Data(String, Vec<(String, bool)>),
    Definition {
        name: String,
        parameters: Vec<(String, Expr)>,
        result: Expr,
        body: Expr,
    },
}

struct Token {
    text: String,
    line: usize,
}

pub(crate) fn parse(source: &str) -> Result<Vec<Declaration>, Error> {
    let mut tokens = Vec::new();
    let mut chars = source.chars().peekable();
    let mut line = 1;
    while let Some(c) = chars.next() {
        if c == '\n' {
            line += 1;
            continue;
        }
        if c.is_whitespace() {
            continue;
        }
        if c == '-' && chars.peek() == Some(&'-') {
            for c in chars.by_ref() {
                if c == '\n' {
                    line += 1;
                    break;
                }
            }
            continue;
        }
        let mut text = c.to_string();
        if c.is_ascii_alphabetic() || c == '_' {
            while let Some(&c) = chars.peek() {
                if !c.is_ascii_alphanumeric() && c != '_' && c != '.' && c != '\'' {
                    break;
                }
                text.push(c);
                chars.next();
            }
        } else if (c == ':' && chars.peek() == Some(&'='))
            || (c == '=' && chars.peek() == Some(&'>'))
        {
            text.push(chars.next().unwrap());
        } else if !"():;|=".contains(c) {
            return Err(Error(format!("line {line}: unsupported character {c:?}")));
        }
        tokens.push(Token { text, line });
    }
    let mut parser = Parser { tokens, at: 0 };
    let mut declarations = Vec::new();
    while parser.peek().is_some() {
        declarations.push(parser.declaration()?);
    }
    Ok(declarations)
}

struct Parser {
    tokens: Vec<Token>,
    at: usize,
}

impl Parser {
    fn peek(&self) -> Option<&str> {
        self.tokens.get(self.at).map(|t| t.text.as_str())
    }

    fn error(&self, message: &str) -> Error {
        let line = self
            .tokens
            .get(self.at)
            .map(|t| t.line)
            .unwrap_or_else(|| self.tokens.last().map(|t| t.line).unwrap_or(1));
        Error(format!("line {line}: {message}"))
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
        if self.eat("inductive") {
            let name = self.name()?;
            self.expect("where")?;
            let mut constructors = Vec::new();
            while self.eat("|") {
                let constructor = self.name()?;
                let recursive = self.eat("(");
                if recursive {
                    self.name()?;
                    self.expect(":")?;
                    self.expect(&name)?;
                    self.expect(")")?;
                }
                constructors.push((constructor, recursive));
            }
            return Ok(Declaration::Data(name, constructors));
        }
        if !self.eat("def") && !self.eat("theorem") {
            return Err(self.error("expected inductive, def or theorem"));
        }
        let name = self.name()?;
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
        self.expect(":")?;
        let result = self.expression()?;
        self.expect(":=")?;
        let body = self.expression()?;
        Ok(Declaration::Definition {
            name,
            parameters,
            result,
            body,
        })
    }

    fn expression(&mut self) -> Result<Expr, Error> {
        if self.eat("let") {
            let name = self.name()?;
            self.expect(":")?;
            let ty = self.expression()?;
            self.expect(":=")?;
            let value = self.expression()?;
            self.expect(";")?;
            let body = self.expression()?;
            return Ok(Expr::Let(
                name,
                Box::new(ty),
                Box::new(value),
                Box::new(body),
            ));
        }
        self.eat("by");
        self.eat("exact");
        let lhs = self.application()?;
        if self.eat("=") {
            let rhs = self.application()?;
            Ok(Expr::Equal(Box::new(lhs), Box::new(rhs)))
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
        match head {
            Expr::Name(name, mut previous) => {
                previous.extend(args);
                Ok(Expr::Name(name, previous))
            }
            Expr::Equal(_, _) | Expr::Refl | Expr::Rec { .. } | Expr::Let(_, _, _, _) => {
                Err(self.error("only named contextual terms can be applied"))
            }
        }
    }

    fn atom(&mut self) -> Result<Expr, Error> {
        if self.eat("(") {
            let result = self.expression()?;
            self.expect(")")?;
            return Ok(result);
        }
        if self.eat("rfl") {
            return Ok(Expr::Refl);
        }
        if self.eat("rec") {
            let scrutinee = self.application()?;
            self.expect("motive")?;
            self.expect("(")?;
            let variable = self.name()?;
            self.expect(":")?;
            let data = self.name()?;
            self.expect(")")?;
            self.expect("=>")?;
            let motive = self.expression()?;
            self.expect("with")?;
            let mut cases = Vec::new();
            while self.eat("|") {
                let constructor = self.name()?;
                let mut variables = Vec::new();
                while self.peek() != Some("=>") {
                    variables.push(self.name()?);
                }
                self.expect("=>")?;
                let body = self.expression()?;
                cases.push(Case {
                    constructor,
                    variables,
                    body,
                });
            }
            self.expect("end")?;
            return Ok(Expr::Rec {
                scrutinee: Box::new(scrutinee),
                variable,
                data,
                motive: Box::new(motive),
                cases,
            });
        }
        Ok(Expr::Name(self.name()?, Vec::new()))
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
