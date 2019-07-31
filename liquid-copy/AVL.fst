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

(*
val all_less_than : k:int -> t:tree -> Tot bool
let all_less_than k t = all_tree (less_k k) t

val all_more_than : k:int -> t:tree -> Tot bool
let all_more_than k = all_tree (more_k k)*)

val all_more_than : x:int -> t:tree -> Tot bool
let rec all_more_than x = function 
| Leaf -> true
| Node y l r _ -> y > x && all_more_than x l && all_more_than x r 

val all_less_than : x:int -> t:tree -> Tot bool
let rec all_less_than x = function 
| Leaf -> true
| Node y l r _ -> y < x && all_more_than x l && all_more_than x r 


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

val mk_node : v:int -> l:(avll v) -> r:(r':avlr v {has_bal 1 l r'}) -> Tot (t:avln (node_height l r ))
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

val balL0 : x:int -> l:avll x {is_not_heavy l && not_empty l} -> r:avlr x {is_left_big l r} -> avln (real_height l + 1)
let balL0 x (Node lv ll lr _) r = 
  let y = mk_node x lr r in  
  mk_node lv ll y

val balLL : x:int -> l:avll x {is_left_heavy l} -> r:avlr x {is_left_big l r} -> avlt l
let balLL v (Node lv ll lr _) r = mk_node lv ll (mk_node v lr r)

(*
val balLR :x:int  -> l:avll x {is_right_heavy l} -> r:avlr x {is_left_big l r} -> avlt l
let balLR v (Node lv ll (Node lrv lrl lrr _) _) r
  = let y = mk_node v lrr r in
    assert (all_more_than lrv lrr );
    
    assert (all_more_than lrv r);
    assert (lv < v);
    
    mk_node lrv (mk_node lv ll lrl) (y) *)

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

val all_more_than_2: t:tree -> k:int -> Tot bool
let all_more_than_2 = function
  | Leaf  -> fun x . true
  | Node v l r _ -> fun k. = v > k && all_more_than_2 l k && all_more_than_2 r k

val all_more_intro_2 = v:int -> x:int {x > v} -> l:avll x {all_more_than_2 l v} -> r:avlr x{all_more_than r v} -> Lemma (all_more_than_2 (mk_node x l r) v)
let all_more_intro_2 = ()

val balR0 : x:int  -> r:avlr x {is_not_heavy r && not_empty r} -> l:avll x {is_right_big l r} -> avln (real_height l + 1)
let balR0 x (Node rv rl rr _) l = mk_node rv (mk_node x l rl) rr
 
val bal : x:int -> l:avll x -> r:avlr x {has_bal 2 l r} -> t:avl {re_bal l r t}
let bal x l r = admit ()
