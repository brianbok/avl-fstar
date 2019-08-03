module CantProveBst
open FStar.Tactics

type tree =
     | Leaf : tree
     | Node : key:int -> l:tree -> r:tree -> ah:int -> tree

val all_tree : f:(int-> Tot bool) -> tree -> Tot bool
let rec all_tree f = function
    | Leaf -> true
    | (Node k l r _) -> f k && all_tree f l && all_tree f r 

val all_less_than : k:int -> t:tree -> Tot bool
let all_less_than k t = all_tree (fun x -> x < k) t

val all_more_than : k:int -> t:tree -> Tot bool
let all_more_than k t = all_tree (fun x -> x > k) t

val is_bst : tree -> Tot bool
let rec is_bst = function
    | Leaf -> true
    | (Node k l r _) -> all_tree (fun x -> x < k) l && all_tree (fun x -> x > k) r && is_bst l && is_bst r

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


val has_bal : int -> tree -> tree -> Tot bool
let has_bal x l r =
  let d = real_height l - real_height r in
  0 - x <= d && d <= x

val is_bal : tree -> Tot bool
let is_bal = function
  | Leaf -> true
  | Node _ l r _ -> has_bal 1 l r

val is_avl : tree -> Tot bool
let is_avl t = is_bst t && has_real_heights t && is_bal t

type avl = t:tree {is_avl t}

let get_height = function
  | Leaf -> 0
  | Node _ _ _ n -> n


(* trees of height N *)
type avln (n:int) = t:avl {real_height t = n} 
(* trees of height equal to that of another T *)
type avlt (#t:tree) = t':avl {real_height t' = real_height t}
type avll (k:int) = t:avl {all_tree (fun x -> x < k) t} 
(* trees of height equal to that of another T *)
type avlr (k:int) = t:avl {all_tree (fun x -> x > k) t}

val empty : avln 0
let empty = Leaf

val singleton : int -> avln 1
let singleton x =  Node x empty empty 1

val mk_node : v:int -> l:(avll v) -> r:(r':avlr v {has_bal 1 l r'}) -> Tot tree
let mk_node v l r = 
 let hl = get_height l in
 let hr = get_height r in
 let h = 1 + max hl hr in
   assert (has_real_heights (Node v l r h));
   assert (is_bal (Node v l r h));
   assert (all_tree (fun x -> x < v ) l );
   assert (all_tree (fun x -> x > v ) r );
   assert (is_bst r );
   assert (is_bst l );
   assert (is_bst (Node v l r h));   

   Node v l r h 
      