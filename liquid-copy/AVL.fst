module AVL
open FStar.Tactics

type tree =
     | Leaf : tree
     | Node : key:int -> l:tree -> r:tree -> ah:int -> tree

val all_tree : f:(int-> Tot bool) -> tree -> Tot bool
let rec all_tree f = function
    | Leaf -> true
    | (Node k l r _) -> f k && all_tree f l && all_tree f r 

val less_k : k:int -> x:int -> Tot bool
let less_k k x = x < k 

val more_k : k:int -> x:int -> Tot bool
let more_k k x = x > k 

val all_more_than : k:int -> t:tree -> Tot bool
let rec all_more_than k = function 
| Leaf -> true
| Node y l r _ -> y > k && all_more_than k l && all_more_than k r 

val all_less_than : k:int -> t:tree -> Tot bool
let rec all_less_than k = function 
| Leaf -> true
| Node y l r _ -> y < k && all_less_than k l && all_less_than k r 


val is_bst : tree -> Tot bool
let rec is_bst = function
    | Leaf -> true
    | (Node k l r _) -> all_less_than k l && all_more_than k r && is_bst l && is_bst r

val max : x:int -> y:int -> Tot (r:int {r = x \/ r = y})
let max x y = if x > y then x else y

val real_height : t:tree -> Tot int

let rec real_height = function
  | Leaf -> 0
  | Node _ l r _ -> 
    let hl = real_height l in
    let hr = real_height r in
    1 + max hl hr 

val node_height : tree -> tree -> Tot int
let node_height l r = 
  let hl = real_height l in
  let hr = real_height r in
  1 + max hl hr 

val is_real_h : int -> tree -> tree -> Tot bool
let is_real_h v l r = v = node_height l r

val has_real_heights : tree -> Tot bool
let rec has_real_heights = function 
  | Leaf -> true
  | Node _ l r ah -> is_real_h ah l r && has_real_heights l && has_real_heights r

val get_height : t:tree {has_real_heights t} -> Tot int
let get_height = function
    |Leaf -> 0
    | Node _ _ _ h -> h  
    
val has_bal : int -> tree -> tree -> Tot bool
let has_bal x l r =
  let d = real_height l - real_height r in
  0 - x <= d && d <= x

val is_bal : tree -> Tot bool
let rec is_bal = function
  | Leaf -> true
  | Node _ l r _ -> has_bal 1 l r && is_bal l && is_bal r

val is_avl : tree -> Tot bool
let is_avl t = is_bst t && has_real_heights t && is_bal t

type avl = t:tree {is_avl t}

(* trees of height N *)
type avln (n:int) = t:avl {real_height t = n} 
(* trees of height equal to that of another T *)
type avlt (t:tree) = t':avln (real_height t)
type avll (k:int) = t:avl {all_less_than k t} 
(* trees of height equal to that of another T *)
type avlr (k:int) = t:avl {all_more_than k t}

val empty : avln 0
let empty = Leaf

val singleton : int -> avln 1
let singleton x =  Node x empty empty 1

val mk_node : v:int -> l:(avll v) -> r:avlr v {has_bal 1 l r} -> Tot (avln (node_height l r ))
let mk_node v l r = 
 let hl = get_height l in
 let hr = get_height r in
 let h = 1 + max hl hr in
   Node v l r h 

val is_empty : t:tree -> Tot bool
let is_empty = function
  | Leaf -> true
  | Node _ _ _ _ -> false

val not_empty : t:tree -> Tot bool
let not_empty t = not (is_empty t)

val head: t:tree {not_empty t} -> Tot int
let head (Node x _ _ _) = x

val left: t:tree {not_empty t} -> Tot tree
let left (Node _ l _ _) = l 


val right: t:tree {not_empty t} -> Tot tree
let right (Node _ _ r _) = r


val left_of_avl_is_avll : t:avl{not_empty t} -> y:int {y == head t } -> Lemma(all_less_than y (left t))
let left_of_avl_is_avll t y = ()

(*
val insert : x:int -> t:avl -> Tot avl
let rec insert x = function
  | Leaf -> singleton x
  | Node y l r h -> 
    if x < y 
    then begin
      left_of_avl_is_avll (Node y l r h) y;
      mk_node y (insert x l) r
    end 
    else mk_node y l (insert x r)
*)

val diff : s:tree {has_real_heights s} -> t:tree {has_real_heights t} -> Tot int 
let diff s t = get_height s - get_height t

val get_balfac : t:tree {has_real_heights t} -> Tot int
let get_balfac = function 
  | Leaf -> 0
  | Node _ l r _ -> diff l r

val is_left_heavy : t:tree{has_real_heights t} -> Tot bool
let is_left_heavy t = get_balfac t > 0

val is_right_heavy : t:tree {has_real_heights t} -> Tot bool
let is_right_heavy t = get_balfac t < 0

val is_not_heavy : t:tree {has_real_heights t} -> Tot bool
let is_not_heavy t = get_balfac t = 0

val is_left_big: l:tree{has_real_heights l} -> r:tree{has_real_heights r} -> Tot bool 
let is_left_big l r = diff l r = 2

val is_right_big : l:tree{has_real_heights l} -> r:tree{has_real_heights r} -> Tot bool
let is_right_big l r = diff r l = 2


val all_more_intro_p: v:int -> x:int {x > v} -> l:tree {all_more_than x l} -> Lemma (all_more_than v l)
let all_more_intro_p v x l = admit ()


val all_less_intro_p: v:int -> x:int {x <= v} -> l:tree {all_less_than x l} -> Lemma (all_less_than v l)
let all_less_intro_p v x l = admit ()

val all_more_intro: v:int -> x:int {x > v} -> l:avll x {all_more_than v l} -> r:avlr x{all_more_than v r && has_bal 1 l r} -> Lemma (all_more_than v (mk_node x l r))
let all_more_intro v x l r  = ()

val all_less_intro: v:int -> x:int {x < v} -> l:avll x {all_less_than v l} -> r:avlr x {all_less_than v r && has_bal 1 l r} -> Lemma ((all_less_than v (mk_node x l r)))
let all_less_intro v x l r  = ()

val balL0 : x:int -> l:avll x {is_not_heavy l} -> r:avlr x {is_left_big l r} -> avln (real_height l + 1)
let balL0 x l r = match l with 
  | (Node lv ll lr _) -> 
    let y = mk_node x lr r in
    all_more_intro_p lv x r;
    mk_node lv ll y
  | _ -> admit ()

val balLL : x:int -> l:avll x {is_left_heavy l} -> r:avlr x {is_left_big l r} -> avlt l
let balLL v (Node lv ll lr _) r =
  all_more_intro_p lv v r;
  mk_node lv ll (mk_node v lr r)

val eq_or_up : s:tree{has_real_heights s} -> t:tree{has_real_heights t} -> Tot bool
let eq_or_up s t = 
  let d = diff t s in
  d = 0 || d = 1

val bal_ht : l:tree -> r:tree -> t:tree -> Tot bool
let bal_ht l r t = not (has_bal 1 l r) || is_real_h (real_height t) l r

val big_ht : l:tree{has_real_heights l} -> r:tree{has_real_heights r} -> t:tree{has_real_heights t} -> Tot bool 
let big_ht l r t = 
  let hl = real_height l in
  let hr = real_height r in
  let l_big    = not (hl >= hr) || (eq_or_up l t) in
  let r_big    = (hl >= hr)     || (eq_or_up r t) in
  l_big && r_big

val re_bal : l:tree {has_real_heights l} -> r:tree {has_real_heights r} -> t:tree{has_real_heights t} -> Tot bool  
let re_bal l r t = big_ht l r t && bal_ht l r t

val transitividad : a:int -> b:int {b > a} -> c:int {b < c} -> Lemma (a < c)
let transitividad a b c = ()

val balLR :x:int  -> l:avll x {is_right_heavy l} -> r:avlr x {is_left_big l r} -> Tot (avlt l)
let balLR v l r = match l with
  | (Node lv ll (Node lrv lrl lrr lrh) lh) -> 
    let y = mk_node v lrr r in
       
    all_more_intro_p lrv v r;
    all_less_intro_p lrv lv ll; 

    mk_node lrv (mk_node lv ll lrl) (y)
  | _ -> 
    (* assert (! (is_right_heavy l)); *)
    
    admit()


val balR0 : x:int  -> r:avlr x {is_not_heavy r} -> l:avll x {is_right_big l r} -> Tot (avln (real_height r + 1))
let balR0 x r l = match r with 
  | (Node rv rl rr _) ->
    all_less_intro_p rv x l;
    mk_node rv (mk_node x l rl) rr
  | _ -> 
    admit ()


val balRR : x:int -> l:avll x -> r:avlr x {is_right_big l r && is_right_heavy r} -> Tot (avlt r)
let balRR x l (Node rv rl rr _) = 
  all_less_intro_p rv x l;
  mk_node rv (mk_node x l rl) rr 

val balRL : x:int -> l: avll x -> r:avlr x {is_right_big l r && is_left_heavy r} -> Tot (avlt r)
let balRL x l = function
  | (Node rv (Node rlv rll rlr _) rr _) -> 
    all_less_intro_p rlv x l;
    all_more_intro_p rlv rv rr;
    mk_node rlv (mk_node x l rll ) (mk_node rv rlr rr)
  | _ -> 
    (* should be impossible *)
    admit ()

val bal : x:int -> l:avll x -> r:avlr x {has_bal 2 l r} -> t:avl {re_bal l r t}
let bal v l r  = 
  let ilb = is_left_big l r in
  let irb = is_right_big l r in
  if (ilb && is_left_heavy l) then balLL v l r
  else if (ilb && is_right_heavy l) then balLR v l r
  else if (ilb) then balL0 v l r
  else if (irb && is_left_heavy r) then balRL v l r
  else if (irb && is_right_heavy r) then balRR v l r
  else if (irb) then balR0 v r l
  else mk_node v l r

val minimum : t:tree {not_empty t} -> Tot int
let rec minimum (Node x l r _) = 
  let lv = if not_empty l then minimum l else x in
  let lr = if not_empty r then minimum r else x in
  min( min x lv) lr


val maximum : t:tree {not_empty t} -> Tot int
let rec maximum (Node x l r _) = 
  let lv = if not_empty l then maximum l else x in
  let lr = if not_empty r then maximum r else x in
  max ( max x lv) lr

val maximum_all_less_lemma : t:tree{not_empty t} -> Lemma (all_less_than (maximum t + 1) t )
let maximum_all_less_lemma t = admit ()

val all_less_minimum_lemma : v:int -> t:tree{all_less_than v t} -> Lemma (not_empty t ==> maximum t < v)
let all_less_minimum_lemma v t = admit ()


val insert: x:int -> s:avl -> Tot (t:avl {not_empty t /\ eq_or_up s t /\ (minimum t = (if is_empty s then x else min x (minimum s))) /\ (maximum t = (if is_empty s then x else max x (maximum s)))}) (decreases s)
let rec insert x t = match t with
  | (Node v l r n) ->
    if x < v then begin
      let insl = insert x l in
      all_less_minimum_lemma v l;
      assert (maximum insl <= v - 1);
      maximum_all_less_lemma insl;
      all_less_intro_p v (maximum insl + 1) insl;
      bal v insl r
    end else if x > v then begin
      bal v l (insert x r)
    end else t
  | Leaf -> singleton x
