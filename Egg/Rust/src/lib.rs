use egg::*;
use std::ffi::{c_char, c_void, CStr, CString};

define_language! { 
    pub enum L { 
        "0" = Zero,
    }
}

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
pub extern "C" fn run_egg(input:  *const c_char) -> *const c_char {
    let input = c_str_to_string(input);
    
    let egraph : EGraph<L,()> = EGraph::default();

    // EggResult {
    //     success: flag,
    //     info: string_to_c_str(format!("{:?}", input)),
    //     egraph: Some(Box::new(egraph))
    // }
    string_to_c_str("huhu".to_string())
}   
