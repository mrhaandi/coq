(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module PriorityQueue : sig
  type 'a t
  val create : unit -> 'a t
  val set_rel : ('a -> 'a -> int) -> 'a t -> unit
  val is_empty : 'a t -> bool
  val exists : ('a -> bool) -> 'a t -> bool
  val pop : ?picky:('a -> bool) -> 'a t -> 'a
  val push : 'a t -> 'a -> unit
  val clear : 'a t -> unit
  val length : 'a t -> int
end = struct
  type 'a item = int * 'a
  type 'a rel = 'a item -> 'a item -> int
  type 'a t = ('a item list * 'a rel) ref
  let sort_timestamp (i,_) (j,_) = i - j
  let age = ref 0
  let create () = ref ([],sort_timestamp)
  let is_empty t = fst !t = []
  let exists p t = List.exists (fun (_,x) -> p x) (fst !t)
  let pop ?(picky=(fun _ -> true)) t =
    let (l, rel) = !t in
    let rec aux acc = function
      | [] -> raise Queue.Empty
      | (_,x) :: xs when picky x -> t := (List.rev acc @ xs, rel); x
      | (_,x) as hd :: xs -> aux (hd :: acc) xs in
    aux [] l
  let push t x =
    let (xs, rel) = !t in
    incr age;
    (* re-roting the whole list is not the most efficient way... *)
    t := (List.sort rel (xs @ [!age,x]), rel)
  let clear t = t := ([], snd !t)
  let set_rel rel t =
    let rel (_,x) (_,y) = rel x y in
    t := (List.sort rel (fst !t), rel)
  let length t = List.length (fst !t)
end

type 'a t = {
  queue: 'a PriorityQueue.t;
  lock : Mutex.t;
  cond : Condition.t;
  mutable nwaiting : int;
  cond_waiting : Condition.t;
  mutable release : bool;
}

exception BeingDestroyed

let create () = {
  queue = PriorityQueue.create ();
  lock = Mutex.create ();
  cond = Condition.create ();
  nwaiting = 0;
  cond_waiting = Condition.create ();
  release = false;
}

let pop ?(picky=(fun _ -> true)) ?(destroy=ref false) tq =
  let { queue = q; lock = m; cond = c; cond_waiting = cn } = tq in
  Mutex.lock m;
  if tq.release then (Mutex.unlock m; raise BeingDestroyed);
  while not (PriorityQueue.exists picky q || !destroy) do
    tq.nwaiting <- tq.nwaiting + 1;
    Condition.broadcast cn;
    Condition.wait c m;
    tq.nwaiting <- tq.nwaiting - 1;
    if tq.release || !destroy then (Mutex.unlock m; raise BeingDestroyed)
  done;
  if !destroy then (Mutex.unlock m; raise BeingDestroyed);
  let x = PriorityQueue.pop ~picky q in
  Condition.signal c;
  Condition.signal cn;
  Mutex.unlock m;
  x

let broadcast tq =
  let { lock = m; cond = c } = tq in
  Mutex.lock m;
  Condition.broadcast c;
  Mutex.unlock m

let push tq x =
  let { queue = q; lock = m; cond = c; release } = tq in
  if release then CErrors.anomaly(Pp.str
    "TQueue.push while being destroyed! Only 1 producer/destroyer allowed.");
  Mutex.lock m;
  PriorityQueue.push q x;
  Condition.broadcast c;
  Mutex.unlock m

let length tq =
  let { queue = q; lock = m } = tq in
  Mutex.lock m;
  let n = PriorityQueue.length q in
  Mutex.unlock m;
  n

let clear tq =
  let { queue = q; lock = m; cond = c } = tq in
  Mutex.lock m;
  PriorityQueue.clear q;
  Mutex.unlock m

let clear_saving tq f =
  let { queue = q; lock = m; cond = c } = tq in
  Mutex.lock m;
  let saved = ref [] in
  while not (PriorityQueue.is_empty q) do
    let elem = PriorityQueue.pop q in
    match f elem with
    | Some x -> saved := x :: !saved
    | None -> ()
  done;
  Mutex.unlock m;
  List.rev !saved

let is_empty tq = PriorityQueue.is_empty tq.queue

let destroy tq =
  tq.release <- true;
  while tq.nwaiting > 0 do
    Mutex.lock tq.lock;
    Condition.broadcast tq.cond;
    Mutex.unlock tq.lock;
  done;
  tq.release <- false

let wait_until_n_are_waiting_and_queue_empty j tq =
  Mutex.lock tq.lock;
  while not (PriorityQueue.is_empty tq.queue) || tq.nwaiting < j do
    Condition.wait tq.cond_waiting tq.lock
  done;
  Mutex.unlock tq.lock

let wait_until_n_are_waiting_then_snapshot j tq =
  let l = ref [] in
  Mutex.lock tq.lock;
  while not (PriorityQueue.is_empty tq.queue) do
    l := PriorityQueue.pop tq.queue :: !l
  done;
  while tq.nwaiting < j do Condition.wait tq.cond_waiting tq.lock done;
  List.iter (PriorityQueue.push tq.queue) (List.rev !l);
  if !l <> [] then Condition.broadcast tq.cond;
  Mutex.unlock tq.lock;
  List.rev !l

let set_order tq rel =
  Mutex.lock tq.lock;
  PriorityQueue.set_rel rel tq.queue;
  Mutex.unlock tq.lock
