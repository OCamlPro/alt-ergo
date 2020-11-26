// This files aims to give missing primitives to js_of_ocaml compiler
// the missing primitives are replace with dummies

//Provides: unix_times
//Requires: unix_gettimeofday
function unix_times () {
    var utime = unix_gettimeofday ();
    return BLOCK(0, utime, utime, utime, utime)
}
//Provides: unix_setitimer
function unix_setitimer () {
  return BLOCK(0, 0, 0, 0)
}

// Camlzip primitives
//Provides: camlzip_inflateEnd
function  camlzip_inflateEnd () {
  return BLOCK(0, 0, 0, 0)
}
//Provides: camlzip_inflateInit
function camlzip_inflateInit () {
  return BLOCK(0, 0, 0, 0)
}
//Provides: camlzip_inflate_bytecode
function camlzip_inflate_bytecode () {
  return BLOCK(0, 0, 0, 0)
}
//Provides: camlzip_update_crc32
function camlzip_update_crc32 () {
  return BLOCK(0, 0, 0, 0)
}