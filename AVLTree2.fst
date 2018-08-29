module AVLTree2

val max : int -> int -> Tot int
let max i1 i2 = if i1 > i2 then i1 else i2
let _ = assert (forall x y. max x y >= x
                && max x y >= y
                && (max x y = x || max x y = y))

type avltree =
  | E : avltree
  | T : key:int -> lt:avltree -> lth:nat -> rt:avltree -> rth:nat -> avltree

val height: avltree -> Tot nat

let rec height t = 
	match t with
	| E -> 1
	| T _ t1 h1 t2 h2 -> (max h1 h2) + 1
	
val is_empty: avltree -> bool
let is_empty t =
	match t with 
	| E -> true
	| _ -> false
	
type empty_tree = t:avltree{is_empty t}
type nonempty_tree = t:avltree{not (is_empty t)}

val in_tree : int -> avltree -> Tot bool
let rec in_tree x t =
  match t with
  | E -> false
  | T n t1 h1 t2 h2 -> x = n || in_tree x t1 || in_tree x t2

val all : p:(int -> Tot bool) -> t:avltree ->
            Tot (r:bool{r <==> (forall x. in_tree x t ==> p x)})
let rec all p t =
  match t with
  | E -> true
  | T n t1 h1 t2 h2 -> p n && all p t1 && all p t2

(*
 * finally, this is the binary search tree invariant
 * i.e. all elements in the left subtree are smaller than the root key
 * and all elements in the right subtree are greater than the root key
 *)
val k_inv : avltree -> Tot bool
let rec k_inv t =
  match t with
  | E -> true
  | T n t1 _ t2 _ -> all (fun n' -> n' < n) t1 &&
                    all (fun n' -> n' > n) t2 && k_inv t1 && k_inv t2

val create_tree: n:int -> avltree 
    -> avltree -> Tot avltree
let create_tree n t1 t2 = T n t1 (height t1) t2 (height t2)

val bf: avltree -> int
let bf t = match t with
    | E -> 0
    | T _ _ h1 _ h2 -> h2 - h1

val b_inv: t:avltree -> Tot bool
let rec b_inv t =
    match t with
    | E -> true
    | T n t1 h1 t2 h2 -> b_inv t1 && b_inv t2 &&
                    abs (bf t) <= 1

val search : x:int -> t:avltree{k_inv t} ->
  Tot (r:bool{r <==> in_tree x t})
let rec search x t =
  match t with
  | E -> false
  | T n t1 h1 t2 h2 -> if x = n then      true
                    else if x < n then search x t1
                    else               search x t2

val rebalance: t:avltree -> Tot avltree
let rec rebalance t = 
  if abs(bf t) <= 1 then t
  else match t with
      T _ tl hl tr hr ->
          if bf t = 2 then
            if bf tl <> -1 then left_rotate t
            else left_rotate (right_rotate t)
          else 
            if bf tr <> -1 then 
            else t


let ins_inv x t r = (forall y. in_tree y r <==> (in_tree y t \/ x = y))

val insert_avl: x:int -> t:avltree -> 
  Tot (r:avltree{ins_inv x t r })

let rec insert_avl x t = 
    rebalance (match t with
  | E -> create_tree x E E
  | T n t1 h1 t2 h2 -> if x = n then      t
                    else if x < n then create_tree n (insert_avl x t1) t2
                    else               create_tree n t1 (insert_avl x t2))

let can_left_rot t = match t with
    | T _ _ _ (T _ _ _ _ _) _ -> true
    | otherwise -> false

val left_rotate: t:avltree{can_left_rot t} -> r:avltree
let left_rotate (T x a_tree _ (T y b_tree _ c_tree _) _) =
  create_tree y (create_tree x a_tree b_tree) c_tree

let can_right_rot t = match t with
    | T _ (T _ _ _ _ _) _ _ -> true
    | otherwise -> false

val right_rotate: t:avltree{can_right_rot t} -> r:avltree
let right_rotate (T y (T x a_tree _ b_tree _) c_tree _  =
  create_tree y (create_tree x a_tree b_tree) c_tree


type avl_inv (t:avltree) = k_inv t /\ b_inv t

type case_A (t:avltree) = 
	bf t = 2 /\
	bf (T?.rt t) = 1 /\
	b_inv (T?.rt t) /\
	b_inv (T?.lt t)


val hint1: t:avltree{case_A t} -> r:avltree
-> Lemma
(requires case_A t /\ r = left_rotate t)
(ensures (T? r  /\ b_inv (T?.rt r) /\ b_inv (T?.lt (T?.lt r))
/\ b_inv (T?.rt (T?.lt r))) /\
T? t /\
T?.rt r = T?.rt (T?.rt t) /\
height (T?.rt r) = height (T?.lt (T?.rt t)) + 1  /\
height (T?.lt r) = height (T?.lt (T?.rt t)) + 1
(* height (T?.lt t) = height (T?.lt (T?.rt t)) /\
height (T?.lt (T?.lt r)) = height (T?.rt (T?.lt r)) /\
*)
)
let hint1 t r = () 

val lrb: t:avltree ->
    Pure avltree
    (requires(case_A t))   
    (ensures(fun r -> b_inv r))
let lrb t =
    let r = left_rotate t in
    	hint1 t r;
	r