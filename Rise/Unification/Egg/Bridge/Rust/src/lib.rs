use std::ffi::{c_char, CStr, CString};
pub mod lang;

// Cf. https://doc.rust-lang.org/stable/std/ffi/struct.CStr.html#examples
fn c_str_to_string(c_str: *const c_char) -> String {
    let str = unsafe { CStr::from_ptr(c_str) };
    String::from_utf8_lossy(str.to_bytes()).to_string()
}

// TODO: I think this is a memory leak right now.
fn string_to_c_str(str: String) -> *const c_char {
    let expl_c_str = CString::new(str).expect("conversion of Rust-string to C-string failed");

    expl_c_str.into_raw()
}

#[no_mangle]
pub extern "C" fn run_egg(input: *const c_char) -> *const c_char {
    let input = c_str_to_string(input);
    let output = run(&input);
    match output {
        Ok(s) => string_to_c_str(format!("{s}")),
        Err(s) => string_to_c_str(format!("{s}")),
        // Ok(s) => string_to_c_str(format!("!{input}!{s}")),
        // Err(s) => string_to_c_str(format!("?{s}")),
    }

    // next steps:
    // - check that the unify eclass only has [x,x] nodes and no [x,y] nodes
    // - find the mvar class(es)
    // - find the "most concrete terms" and generate substitution
    // - stringify substitution, return it, and parse it with lean.

    // string_to_c_str(format!("fail"))
    // string_to_c_str(format!("ok"))
}

fn run(input: &str) -> Result<String, String> {
    // .map(|x| x.split_once('=').ok_or(format!("invalid input: {input}"))?);

    let res = lang::unify(input)?
        .iter()
        .map(|(k, v)| format!("{}={}", k, v))
        .collect::<Vec<_>>()
        .join(",");
    let res = Ok(res);
    res
}
