open Unix

let argc = Array.length Sys.argv

let filename = Sys.argv.(1)
let buf = Bytes.create 1024

let rec wr fd bf =
  let r = read fd bf 0 1024 in
  match r with
  | 0 -> None
  | _ ->
      let _ = write stdout bf 0 r in
      wr fd bf


let rec rwwhile n file =
  let fd = openfile file [O_RDONLY] 0o640 in
  let _ = wr fd buf in
  let () = close fd in
  if n <= 1 then None else
      rwwhile (n - 1) Sys.argv.(argc - n + 1)

let op = rwwhile (argc - 1) Sys.argv.(1)
