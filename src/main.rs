mod w;
use w::*;

// Run a test case
fn test(exp: Exp) {
    println!("INPUT: {}", exp);
    let mut env = TypeEnv::new();
    let mut tvg = TypeVarGen::new();

    // insert some predefined functions:
    // + :: int -> int -> int -- binary addition
    env.insert("+".into(),
               Polytype {
                   vars: Vec::new(),
                   ty: tfun(Type::Int, tfun(Type::Int, Type::Int)),
               });
    // - :: int -> int -- unary negation
    env.insert("-".into(),
               Polytype {
                   vars: Vec::new(),
                   ty: tfun(Type::Int, Type::Int),
               });
    match env.type_inference(&exp, &mut tvg) {
        Ok(ty) => println!("OUTPUT: {}", ty),
        Err(e) => println!("FAIL: {}", e),
    }
    println!("");
}

// Helper functions to define programs easily
fn tfun(i: Type, o: Type) -> Type {
    Type::Fun(Box::new(i), Box::new(o))
}
fn bind(name: &str, e1: Exp, e2: Exp) -> Exp {
    Exp::Let(name.into(), Box::new(e1), Box::new(e2))
}
fn abs(var: &str, e: Exp) -> Exp {
    Exp::Abs(var.into(), Box::new(e))
}
fn app(e1: Exp, e2: Exp) -> Exp {
    Exp::App(Box::new(e1), Box::new(e2))
}
fn lit<T>(i: T) -> Exp
    where T: Into<Lit>
{
    Exp::Lit(i.into())
}
fn var(name: &str) -> Exp {
    Exp::Var(name.into())
}

fn main() {
    test(lit(5));
    test(lit("hello"));
    test(lit(true));
    test(app(app(var("+"), lit(1)), lit(2)));
    test(app(app(var("+"), lit(true)), lit(false)));
    test(app(var("-"), lit(5)));
    test(app(var("-"), lit("test")));
    test(bind("id", abs("x", var("x")), var("id")));
    test(bind("five", abs("x", lit(5)), var("five")));
    test(bind("id", abs("x", var("x")), app(var("id"), var("id"))));
    test(bind("id",
              abs("x", bind("y", var("x"), var("y"))),
              app(var("id"), var("id"))));
    test(bind("id",
              abs("x", bind("y", var("x"), var("y"))),
              app(app(var("id"), var("id")), lit(2))));
    test(bind("id", abs("x", app(var("x"), var("x"))), var("id")));
    test(abs("m",
             bind("y", var("m"), bind("x", app(var("y"), lit(true)), var("x")))));
    test(app(lit(2), lit(2)));
    test(abs("a",
             bind("x",
                  abs("b",
                      bind("y", abs("c", app(var("a"), lit(1))), app(var("y"), lit(2)))),
                  app(var("x"), lit(3)))));
    test(app(abs("a",
                 bind("x",
                      abs("b",
                          bind("y", abs("c", app(var("a"), lit(1))), app(var("y"), lit(2)))),
                      app(var("x"), lit(3)))),
             abs("x", var("x"))));

    test(abs("f",
             app(abs("x", app(var("f"), app(var("x"), var("x")))),
                 abs("x", app(var("f"), app(var("x"), var("x")))))));

    test(app(abs("f",
                 app(abs("x", app(var("f"), app(var("x"), var("x")))),
                     abs("x", app(var("f"), app(var("x"), var("x")))))),
             abs("x", var("x"))));
    test(abs("x", abs("y", var("x")))); // true
    test(abs("x", abs("y", var("y")))); // false
    test(bind("id",
              abs("x", var("x")),
              bind("eat2",
                   abs("x", abs("y", lit("foo"))),
                   app(app(var("eat2"), app(var("id"), lit(1))),
                       app(var("id"), lit(true))))));
    test(bind("+",
              abs("x", app(var("+"), var("x"))),
              app(app(var("+"), lit(1)), lit(2))));
    test(app(abs("x", app(var("x"), var("x"))),
             abs("x", app(var("x"), var("x")))));
    test(abs("x", app(var("x"), var("x"))));
    test(app(abs("x", app(var("x"), var("x"))), abs("x", var("x"))));

    // the output on this case is correct but nondeterministic because of the random iteration
    // order of Rust's HashMaps and HashSets
    test(bind("zero",
              abs("f", abs("x", var("x"))),
              bind("succ",
                   abs("n",
                       abs("f",
                           abs("x", app(var("f"), app(app(var("n"), var("f")), var("x")))))),
                   app(var("succ"),
                       app(var("succ"),
                           app(var("succ"),
                               app(var("succ"),
                                   app(var("succ"),
                                       app(var("succ"),
                                           app(var("succ"),
                                               app(var("succ"),
                                                   app(var("succ"), var("zero")))))))))))));

    // this case produces an incredibly large type
    test(bind("zero",
              abs("f", abs("x", var("x"))),
              bind("succ",
                   abs("n",
                       abs("f",
                           abs("x", app(var("f"), app(var("n"), app(var("f"), var("x"))))))),
                   app(var("succ"),
                       app(var("succ"),
                           app(var("succ"),
                               app(var("succ"),
                                   app(var("succ"),
                                       app(var("succ"),
                                           app(var("succ"),
                                               app(var("succ"),
                                                   app(var("succ"), var("zero")))))))))))));
}
