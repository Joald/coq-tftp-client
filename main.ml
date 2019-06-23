let std_out = stdout;;

open Unix
open Printf
open Client

(* Auxiliary definitions *)

let compose f g x = f (g x);;

let exit_err msg = printf msg; exit 1;;

let assign_opt r v = r := Some v;;

let nr_to_char nr = Char.chr (Char.code '0' + nr);;

let char_to_nr c = Char.code c - Char.code '0';;

let max_packet_len = 1024;;

let unwrap opt =
  match opt with
  | Some x -> x
  | None -> exit_err "bad option access\n";;

let default d opt =
  match opt with
  | Some x -> x
  | None -> d;;

(* Mutable state of the program *)

let address = ref "";; (* !address : string *)

let in_file = ref "";; (* !in_file : string *)

let out_file = ref "";; (* !out_file : string *)

let current_mode = ref Read;; (* !current_mode : mode *)

let local_file = ref None;; (* !local_file : file_descr *)

(* Program arguments *)

let set_mode new_mode = 
  current_mode := match new_mode with
    | "read"  -> printf "mode: read\n"; Read
    | "write" -> printf "mode: write\n"; Write
    | _       -> exit_err "invalid file mode: must be read or write"
;;

let args = [
  ("-a", Arg.String ((:=) address), "The address of the server.");
  ("-i", Arg.String ((:=) in_file), "The name of the input file.");
  ("-o", Arg.String ((:=) out_file), "The name of the input file.");
  ("-m", Arg.String set_mode, "The mode of file transfer, \"read\" or \"write\".")
];;

(* Coq datatypes interface *)

(* From http://caml.inria.fr/pub/old_caml_site/FAQ/FAQ_EXPERT-eng.html#strings *)
let explode (s : string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

(* From https://stackoverflow.com/questions/29957418/how-to-convert-char-list-to-string-in-ocaml *)
let implode (cl : char list) : string = String.concat "" (List.map (String.make 1) cl);;

(* Network communication *)
let send_bytes (fd : file_descr) (addr : sockaddr) (pac : char list) =
  let packet = implode pac in
    handle_unix_error sendto_substring fd packet 0 (String.length packet) [] addr;;

let modify_port (addr : sockaddr) p : sockaddr =
    match addr with
    | ADDR_INET (addr_inet, _) -> ADDR_INET (addr_inet, int_of_pos p)
    | _ -> exit_err "Invalid address type.";;

let write_to_file (contents : char list) =
    handle_unix_error write_substring (unwrap !local_file) (implode contents) 0 (List.length contents);;

let sockaddr_to_port (addr : sockaddr) =
    match addr with
    | ADDR_INET (_, p) -> p
    | _ -> exit_err "Invalid address type.";;

(*
Definition coq_process_packet (pack : string) (st : state) (p : positive) (timeout : bool) : result.
coq_init (rw_mode : mode) (in_file : string) (out_file : string) : result
*)

let init = lazy (coq_init !current_mode (explode !in_file) (explode !out_file));;

let receive_response fd old_addr =
  let buffer = Bytes.create max_packet_len in
  try let (len, addr) = recvfrom fd buffer 0 max_packet_len [] in
    (addr, Bytes.sub_string buffer 0 len, false)
  with Unix_error (EAGAIN, _, _) -> (old_addr, "", true);;

let process_result (fd : file_descr) (addr : sockaddr) (res : result) =
  let st = res.new_state in
  List.iter (
    fun order -> ignore (match order with
      | SEND_PACKET    -> send_bytes fd (modify_port addr (default (pos_of_int 69) st.port)) res.packet_to_send
      | WRITE_CONTENTS -> write_to_file st.file_contents
      | PRINT          -> printf "PRINTING: %s\n" (implode res.packet_to_send); 0
      | SEND_TO p      -> send_bytes fd (modify_port addr p) res.packet_to_send
    )) st.orders;
  st;;

let rec main_loop (fd : file_descr) (addr : sockaddr) (st : state)  =
  if not st.finished then begin
    printf "Main loop!!\nThe port is %d\n" (int_of_pos (default (pos_of_int 666) st.port));
    flush std_out;
    let (rec_addr, pac, timeout) = handle_unix_error receive_response fd addr in
    printf "Processing packet! The last block nr is %d\n remaining file length: %d" (int_of_n st.last_block_id) (int_of_n (n_strlen st.file_contents (n_of_int 0)));
    flush std_out;
    let res = coq_process_packet (explode pac) st (pos_of_int (sockaddr_to_port rec_addr)) timeout in
    printf "Processed packet!\n";
    flush std_out;
    let new_st = process_result fd addr res in
    printf "Processed result!\n";
        flush std_out;
      main_loop fd addr new_st
  end;;

let run_client info =
  let sock_fd = handle_unix_error socket info.ai_family info.ai_socktype info.ai_protocol in
    setsockopt_float sock_fd SO_RCVTIMEO 1.0;
    let init_st = process_result sock_fd info.ai_addr (Lazy.force init) in
    main_loop sock_fd info.ai_addr init_st;;

let main () =
  if Array.length Sys.argv <> 9 then exit_err "Wrong number of arguments!" else
  Arg.parse args (fun _ -> ()) "A simple TFTP client written in Coq written by Jacek Olczyk.";
  if !current_mode = Read then
    assign_opt local_file (handle_unix_error openfile !out_file [O_WRONLY; O_CREAT; O_EXCL] 0o755)
  else begin
    assign_opt local_file (handle_unix_error openfile !in_file [O_RDONLY] 0);
    let max_file_len = 512 * 256 * 256 + 1 in
    let buf = Bytes.create max_file_len in
    let size = handle_unix_error read (unwrap !local_file) buf 0 max_file_len in
    in_file := Bytes.sub_string buf 0 size;
  end;
  printf "File opened!\n";
  Printexc.record_backtrace false;
  let addr_list = handle_unix_error getaddrinfo !address "69"
                    [AI_FAMILY PF_INET; AI_SOCKTYPE SOCK_DGRAM] in
    run_client (List.hd addr_list)
;;
main ();;