// This files aims to give missing primitives to js_of_ocaml compiler
// the missing primitives are replace with dummies

//Provides: unix_times
//Requires: caml_unix_gettimeofday
function unix_times () {
    var utime = caml_unix_gettimeofday ();
    return BLOCK(0, utime, utime, utime, utime)
}
//Provides: unix_setitimer
function unix_setitimer () {
  return BLOCK(0, 0, 0, 0)
}

//Provides: unix_getpid
function unix_getpid() {
  return 0;
}

//Provides: unix_kill
function unix_kill() {
  return 0;
}
