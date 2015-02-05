
open Batteries
open SpiderMonkey

let parsecmd = ref ""

let set_parsecmd s = parsecmd := s

let parse_file filename = 
    let ch = Unix.open_process_in (!parsecmd ^ " " ^ Filename.quote filename) in
    SpiderMonkey.parse_spidermonkey (IO.to_input_channel ch)

let parse s = 
    let filename = File.with_temporary_out (fun o fn -> String.print o s; fn) in
    parse_file filename

