open Unix

let argc = Array.length Sys.argv

let filename = Sys.argv.(1)
let buf = Bytes.create 1024

let rec wr fd bf =
  let r = read fd bf 0 1024 in
  match r with
  | 0 -> ()
  | _ ->
      let _ = write stdout bf 0 r in
      wr fd bf


let rec rwwhile n  =
  let file = Sys.argv.(argc - n)  in
  let fd = openfile file [O_RDONLY] 0o640 in
  let () = wr fd buf in
  let () = close fd in
  if n <= 1 then () else
      rwwhile (n - 1)

let () = rwwhile (argc - 1)
