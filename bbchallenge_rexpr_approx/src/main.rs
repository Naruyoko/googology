use std::{fs::File, io::Write};

mod omega_num;
use omega_num::{consts, OmegaNum};

mod expr;
use expr::*;

mod approximator;
use approximator::*;

fn main() {
    let mut file = File::create("out.txt").unwrap();
    let mut outln = |s: String| {
        println!("{s}");
        file.write((s + "\n").as_bytes()).unwrap();
    };
    outln(format!("Hello, world!"));
    outln(format!(
        "{}",
        OmegaNum::new(100.1, vec![2, 1, 0, 13, 3, 1], false)
    ));
    outln("".to_owned());
    for i in 1..10 {
        outln(format!(
            "{}",
            OmegaNum::arrow(OmegaNum::from(i as f64), OmegaNum::from(i as f64), 2)
        ))
    }
    outln("".to_owned());
    for i in 1..10 {
        outln(format!(
            "{}",
            OmegaNum::arrow(OmegaNum::from(i as f64), OmegaNum::from(i as f64), 3)
        ))
    }
    outln("".to_owned());
    for i in 1..10 {
        outln(format!(
            "{}",
            OmegaNum::arrow(OmegaNum::from(3.0), OmegaNum::from(3.0), i)
        ))
    }
    let a = [
        consts::ZERO,
        consts::ONE,
        OmegaNum::from(2.0),
        OmegaNum::from(3.0),
        OmegaNum::from(4.0),
        OmegaNum::from(10.0),
        OmegaNum::from(100.0),
        OmegaNum::from(1000000.0),
        OmegaNum::from(1e15),
        consts::MAX_SAFE_INTEGER,
        consts::MAX_SAFE_INTEGER + consts::ONE,
        OmegaNum::from(1e100),
        OmegaNum::new(1e10, vec![1], false),
        consts::e_max_safe_integer(),
        consts::ee_max_safe_integer(),
        OmegaNum::new(1.0, vec![10], false),
        OmegaNum::new(1e16, vec![0, 1], false),
        OmegaNum::new(16.0, vec![2, 1], false),
        OmegaNum::new(16.0, vec![1, 2], false),
        OmegaNum::new(16.0, vec![1, 0, 1], false),
    ];
    outln("".to_owned());
    outln("".to_owned());
    for x in &a {
        outln(format!("{} {:?}", x, x))
    }
    #[allow(unused_variables)]
    let opa: &[(
        &str,
        &dyn Fn(&OmegaNum, &OmegaNum) -> bool,
        &dyn Fn(OmegaNum, OmegaNum) -> OmegaNum,
    )] = &[
        ("+", &|x, y| true, &|x, y| x + y),
        ("-", &|x, y| true, &|x, y| x - y),
        ("*", &|x, y| true, &|x, y| x * y),
        ("/", &|x, y| true, &|x, y| x / y),
        ("^", &|x, y| true, &|x, y| x.pow(y)),
        ("l", &|x, y| true, &|x, y| x.logbase(y)),
        ("^^", &|x, y| true, &|x, y| x.tetr(y)),
        ("^^^", &|x, y| true, &|x, y| x.arrow(y, 3)),
        ("^^^^", &|x, y| true, &|x, y| x.arrow(y, 4)),
    ];
    for x in &a {
        for y in &a {
            outln("".to_owned());
            outln(format!("{} , {}", x, y));
            for (label, cond, f) in opa {
                if cond(x, y) {
                    outln(format!("{} {}", label, f(x.clone(), y.clone())))
                }
            }
        }
    }
    for (label, cond, f) in opa {
        outln(format!(""));
        outln(format!("{label}"));
        for x in &a {
            for y in &a {
                if cond(x, y) {
                    outln(format!("{} , {} , {}", x, y, f(x.clone(), y.clone())))
                }
            }
        }
    }
    outln(format!("Done!"));
}
