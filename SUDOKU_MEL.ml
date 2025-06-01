(* 
  TIPE 2024-2025
  Résolution efficace, générique et validée expérimentalement de sudokus

  Mélissandre PARREAU--BOULMÉ
*)





(********************************************************************************************)
(* Définitions du solveur *)

(* type général, sudoku à résoudre avec où sans propag :
   on code un solver générique sur la représentation des solutions partielles grâce au type puzzle 
   (donne essentiellement sa taille, fonction d'insertion et fonction pour défaire les modifications de la grille (undo)) *)
type puzzle= {     
  size : int ;
  rank : int ;
  grille : int array array;
  insert : int->int->int->bool ;
  possibles: int->int->int array;  (*nécessaire pour la propagation, et surtout pour tester les possibilitées pour une case dans un certain  ordre sans en manquer*)
  undo : unit->unit ;
  timeout : int option ; (*limite optionnelle en nombre de undo*)
  valideconjecture4x4 : bool ; (*ajout pour tester expérimentalement conjecture 4x4 : stable par propag => au moins 2 sol*)
}

(*type des fonctions qui vont créer un p_puzzle ou un b_puzzle : type pas vraiment nécessaire*)
type empty_puzzle = int->puzzle ;; (*rank -> puzzle*)

(* type des questions qu'on peut poser au solver *) 
type 'a question = {
  sudoku : puzzle ;
  enregistre: unit -> unit; (* "enregistre" cette solution *)  
  stop : unit -> bool ; (* indique si on s'arrête là *)
  res: unit -> 'a;  (* retourne le résultat (à partir des solutions "enregistrées") *)
  mutable count_undo: int; (*pour statistiques*)
  nb_sol : unit -> int;   (*nb sol enregistrées au fur et a mesure -> validation conjecture 4X4*)
};;



(* Affiche une grille de sudoku pour un utilisateur*)
let imprime g =
  let n=Array.length g -1 in
  for i=0 to n do
    for j=0 to n do
      let c=g.(i).(j) in
      if c=0 then print_char '-' else print_int c ;
      print_char ' ';
    done;
    print_char '\n';
  done ;;


(*crée un puzzle à partir d'une grille et d'une fonction de type empty_puzzle*)
let import empty g =   
  let n=Array.length g in
  let p= empty (int_of_float (Float.sqrt (float_of_int n))) in 
  assert (n=p.size) ;
  for i=0 to n-1 do
    for j=0 to n-1 do
      let e=g.(i).(j) in
      if e<>0
      then (let ebis = p.grille.(i).(j) in 
            if ebis=0 
            then assert (p.insert i j e)
            else (if ebis<>e 
                  then failwith "grille incorrecte" 
                  else Printf.printf "indice en (%d,%d) redondant \n" i j)) (* pas necessaire pour resoudre *)
    done
  done ;
  p ;;



(** QUESTIONS: implémentations du type question *)
(* nombre de solutions *)
let nb_sols pb : int question = 
  let nb = ref 0 in
  {
    sudoku = pb;
    enregistre = (fun _ -> nb:=!nb+1);
    stop = (fun _ -> false) ;
    res = (fun _ -> !nb);
    count_undo = 0;
    nb_sol = (fun _ -> !nb);
  };;

(* les deux premières *)
let cherche_2prem pb : int question =
  let nb = ref 0 in
  {
    sudoku = pb;
    enregistre = (fun _ -> nb:=!nb+1 ; Printf.printf "** Solution %d **\n" !nb; imprime pb.grille; print_newline());
    stop = (fun _ -> !nb = 2) ;
    res = (fun _ -> !nb);
    count_undo = 0;
    nb_sol = (fun _ -> !nb);
  };;

(*copie de l'état de la grille, car si on la mettait directement dans la liste elle serait modifiée par le solveur*)
let export p =
  Array.init p.size (fun i -> Array.init p.size (fun j -> p.grille.(i).(j)));;

(* collecter toutes les solutions *)
let collecte pb : int array array list question =
  let sols = ref [] in
  {
    sudoku = pb;
    enregistre = (fun _ -> Printf.printf "** Solution**\n"; imprime pb.grille; print_newline(); sols:=(export pb)::!sols);
    stop = (fun _ -> false) ;
    res = (fun _ -> List.rev !sols); (* pour les conserver dans l'ordre *)
    count_undo = 0;
    nb_sol = (fun _ -> List.length !sols);
  };;
  
(* collecter une solution *)
let collecte_1 pb : int array array option question =
  let sol = ref None in
  {
    sudoku = pb;
    enregistre = (fun _ -> sol:=Some(export pb));
    stop = (fun _ -> !sol<>None) ;
    res = (fun _ -> !sol);
    count_undo = 0;
    nb_sol = (fun _ -> match !sol with
                       |None -> 0
                       |Some _ -> 1);
  };;




(* fonction auxiliaire au solver qui gère le compteur d'undo et le timeout*)
let incr_undo q =
  match q.sudoku.timeout with
  |Some(limit) when q.count_undo>=limit -> failwith "trop long"
  |_ -> q.count_undo<-q.count_undo+1
;;

(* SOLVER paramétré par des questions *)
let solver_param (q: 'a question) : 'a =
  let rec solver_aux q i j : unit =
    let p=q.sudoku in
    if q.stop() then () 
    else if i=p.size then q.enregistre()
    else if j=p.size then solver_aux q (i+1) 0  
    else if p.grille.(i).(j)=0 then ( 
        let poss = p.possibles i j in 
        let nbi = q.nb_sol() in    (* valide conj 4x4 : nb de sol avant passage ds le for *)
        assert (Array.length poss > 0)  ;
        for k=0 to (Array.length poss)-1 do
          if p.insert i j (poss.(k)) 
          then (solver_aux q i (j+1) ; p.undo () ; incr_undo q)
        done ;
        assert(not(p.valideconjecture4x4) || (q.stop() || q.nb_sol()-nbi>=2))    (*valide conj 4x4 : stable par propag => au moins 2 sol*)
      )
    else solver_aux q i (j+1)
  in
  solver_aux q 0 0 ; q.res()
;;










(*********************************************************************************)
(* Implémentation du type puzzle la plus simple, avec insertion sans propagation *)

(* type de puzzle "basique" *)
type b_puzzle = {
  b_size : int ;  (* N pour un sudoku NxN*)
  b_rank : int ;  (* sqrt(N) *)
  b_grille : int array array ;
  b_lig: bool array array; (* pour chaque valeur e-1, pour lig i, retourne faux si e present en ligne i *)
  b_col: bool array array; (* pour valeur e-1, pour col j, retourne faux si e present en colonne j *)
  b_reg: bool array array; (* pour valeur e-1, pour region r, retourne faux si e present en region r *)
  mutable b_undo: (int * int) list;  (*correspondent aux insertions*)
}


(*calcule n° région associée à la case (x,y) en argument*)
let region r x y =  (*r le rang*)
  (x-x mod r)+(y/r) ;;

(*insertion pour b_puzzle : sans propag*)
let b_insert (p:b_puzzle) x y e =
  let g=p.b_grille in
  assert(g.(x).(y)=0) ;
  let k=e-1 in
  let reg=region p.b_rank x y in
  if p.b_lig.(k).(x) && p.b_col.(k).(y) && p.b_reg.(k).(reg)
  then (g.(x).(y)<-e; p.b_undo<-(x,y)::(p.b_undo); 
        p.b_lig.(k).(x)<-false; p.b_col.(k).(y)<-false; p.b_reg.(k).(reg)<-false; true) 
  else false ;;

(* défaire la dernière insertion effectuée *)
let b_undo (p:b_puzzle)=   
  match p.b_undo with
  |[] -> failwith "rien à défaire.."
  |(x,y)::q -> 
    let k=p.b_grille.(x).(y)-1 in
    let reg=region p.b_rank x y in
    p.b_grille.(x).(y)<-0 ; 
    p.b_lig.(k).(x)<-true ; p.b_col.(k).(y)<-true ; p.b_reg.(k).(reg)<-true ;
    p.b_undo <- q
;;

(*fonction de type empty_puzzle qui transforme un b_puzzle en puzzle*)
let b_empty t0 r = (*t0 : timeout*)
  let n = r*r in
  let p={
    b_size = n ;
    b_rank = r ;
    b_grille = Array.init n (fun _ -> Array.init n (fun _ -> 0)) ;
    b_lig = Array.init n (fun _ -> (Array.init n (fun _ -> true))) ;
    b_col = Array.init n (fun _ -> (Array.init n (fun _ -> true))) ;
    b_reg = Array.init n (fun _ -> (Array.init n (fun _ -> true))) ;
    b_undo = []
  }
  in
  let poss=Array.init n (fun i -> i+1) in
  {
    size = p.b_size ;
    rank = p.b_rank ;
    grille = p.b_grille ;
    insert = b_insert p ;
    possibles = (fun _ _ -> poss) ;
    undo = (fun _ -> b_undo p) ;
    timeout = if t0 then Some(1000000) else None ;
    valideconjecture4x4 = false ;
  }
;;










(*******************************************************************)
(* Fonctions utiles pour la propagation : les ind_set *)

(*ensemble d'indice entiers*)
type ind_set = {    (*utilisé dans la matrice des valeurs possibles*)
  mutable length: int;  (* nombre d'indices dans l'ensemble                                                  *)
  value: int array;     (* tableau de taille n => l'ensemble est donné par value[0..length[ + 1               *)
  pos: int array;       (* tableau de taille n => donne pour chaque indice de [0..n[ sa position dans value *)
};;


let set_create_full (n:int): ind_set = {
  length = n;
  value = Array.init n (fun i -> i);
  pos = Array.init n (fun i -> i);
};;

let set_mem (s: ind_set) (e: int): bool =
  s.pos.(e-1) < s.length;;

let assign s i x =
  s.value.(i) <- x; 
  s.pos.(x) <- i;;

let set_add (s: ind_set) (e: int): unit =
  let x = e-1 in
  assert (s.pos.(x) >= s.length);
  let i = s.pos.(x) in
  let j = s.length in
  if i > j
  then (
    let y = s.value.(j) in
    (* on échange x et y sur les positions i et j *)
    assign s j x;
    assign s i y;
  );
  s.length <- j+1;;

let set_rem (s: ind_set) (e: int): unit =
  let x=e-1 in
  assert (s.pos.(x) < s.length);
  let i = s.pos.(x) in
  let j = (s.length-1) in
  let y = s.value.(j) in
  (* on échange x et y sur les positions i et j *)
  assign s j x;
  assign s i y;
  ;
  s.length <- j;;

let set_first (s: ind_set): int =
  assert (s.length > 0);
  s.value.(0)+1;;

let set_toarray s =
  Array.init s.length (fun i -> s.value.(i)+1) ;;

let set_imprime s = 
  for i=0 to (Array.length s.value)-1 do
    if i = s.length then print_string "|| ";
    Printf.printf "%d " (s.value.(i)+1);
    assert (s.pos.(s.value.(i))=i); (* verif de l'invariant *)
  done;
  if s.length = Array.length s.value then print_string "|| ";
  print_newline();;




(*********************************************************************************)
(* Implémentation du type puzzle avec propagation *)

(*type des actions à défaire sur le sudoku*)
type action =    
  | Insert of int * int   (* Insert i: on a inséré un nombre en case (i,j) *)
  | RemovePoss of int * int * int (* RemoveCol(j, cols): on a effacé e de l'ensemble p_possibles *)
;;

(* type de puzzle utilisé pour propagation*)
type p_puzzle= {  
  p_size : int ;  (* N pour un sudoku NxN*)
  p_rank : int ;  (* sqrt(N) *)
  p_grille : int array array ;
  p_possibles : ind_set array array ;
  mutable p_undo : action list list
} ;;



(* liste des cases adjacentes à une case : utile pour propagation *)
let adjacentes r x y=   (* r le rang : 2 pour un 4x4, 3 pour un 9x9*)
  let m=r*r-1 in (*N-1 pour un NxN : 3 pour un 4x4, 8 pour un 9x9*) 
  let adj=ref [] in
  for a=0 to m do
    if a<>y then adj:=((x,a)::!adj)
  done ;
  for a=0 to m do
    if a<>x then adj:=((a,y)::!adj)
  done ;
  (* adj:=((-9,-9,-9)::!adj) ; *)
  let idep=r*(x/r) and jdep=r*(y/r) in
  for i=idep to (idep+(r-1)) do
    for j=jdep to (jdep+(r-1)) do
      if i<>x && j<>y 
      then adj:=((i,j)::!adj)
    done ;
  done ; !adj ;;


(* pour debogger la propagation : affiche le puzzle en l'état *)
let puzzle_imprime p =
  let n=p.p_size-1 in
  imprime p.p_grille; print_newline();
  for i = 0 to n do
    for j = 0 to n do
      Printf.printf "(%d,%d): " i j; 
      set_imprime p.p_possibles.(i).(j)
    done
  done;
  print_string "----"; 
  print_newline();;


(* fonction d'insertion "intérieure" à p_insert :
   fait l'insertion d'une valeur e dans une case (x,y) telles que données en argument (fonction p_insert)
   et les propagations liées à cette insertion (fonction propag)
   + enregistre les modifications de la grille dans la liste undo en arument
   => renvoie true ssi l'insertion (+propag) est réussie *)
let rec p_insert_aux (p:p_puzzle) undos x y e =
  let g=p.p_grille in
  assert (g.(x).(y)=0) ;
  let poss=p.p_possibles.(x).(y) in
  if (set_mem poss e) then (
    g.(x).(y)<-e ;
    undos := Insert(x,y)::(!undos) ;
    propag p undos x y e )
  else false
and propag (p:p_puzzle) undos x y e=
  let g=p.p_grille in
  let adj=adjacentes p.p_rank x y in
  set_rem p.p_possibles.(x).(y) e ; undos := RemovePoss(e,x,y)::(!undos) ;
  let rec aux adj e =  (* retire e des possibles des cases adj + si singleton -> insertion*)
    match adj with
    |[] -> true
    |(i,j)::q -> if g.(i).(j) <> 0
      then (g.(i).(j)<>e && aux q e) (*e ne peut pas être dans une case adjacente à celle où l'on a inséré e*)
      else (
        let pos=p.p_possibles.(i).(j) in
        if set_mem pos e then (set_rem pos e ; undos := RemovePoss(e,i,j)::(!undos)) ;
        if pos.length = 1 then (p_insert_aux p undos i j (set_first pos) && aux q e) else aux q e
      )
  in
  aux adj e ;;


(*fonction auxiliaire qui inverse les effets d'une liste d'actions sur le puzzle*)
let rec undo_aux p undos =
  match undos with
  |[] -> ()
  |RemovePoss(e,x,y)::q -> (set_add p.p_possibles.(x).(y) e ; undo_aux p q)
  |Insert(i,j)::q -> (p.p_grille.(i).(j)<-0 ; undo_aux p q);;


(*fonction qui défait la dernière liste d'actions de la "liste de listes d'actions" en argument*)
let p_undo (p:p_puzzle)=   
  match p.p_undo with
  |[] -> failwith "rien à défaire.."
  |undos::q -> undo_aux p undos ; p.p_undo <- q ;;


(*fonction d'insertion englobante, 
  réalise l'insertion dans un p_puzzle en mettant à jour les undo dans le champ du puzzle*)
let p_insert p x y e =
  let undos = ref [] in  (* action list de cette insertion en cascade, ajoutée dans p.undo à la fin *)
  if p_insert_aux (p:p_puzzle) undos x y e
  then (p.p_undo <- !undos::p.p_undo ; true) 
  else (undo_aux p !undos; false);;


(* fonction de type empty_puzzle qui transforme un p_puzzle en puzzle pour que le solveur utilise cette 
   structure générique et soit aussi efficace sans propagation *)
let p_empty t0 r =  (*t0 : timeout*)
  let n = r*r in
  let p={
    p_size = n ;
    p_rank = r ;
    p_grille = Array.init n (fun _ -> Array.init n (fun _ -> 0)) ;
    p_possibles = Array.init n (fun _ -> (Array.init n (fun _ -> set_create_full n))) ;
    p_undo = []
  }
  in
  {
    size = p.p_size ;
    rank = p.p_rank ;
    grille = p.p_grille ;
    insert = p_insert p ;
    possibles = (fun i j -> set_toarray p.p_possibles.(i).(j)) ;
    undo = (fun _ -> p_undo p) ;
    timeout = if t0 then Some(60000) else None;
    valideconjecture4x4 = p.p_size=4 ;
  }
;;












(************************************************************)
(* Les grilles testées *)

let sud4_hard = [|
  [|1; 0; 0; 0|];
  [|0; 0; 2; 0|];
  [|3; 1; 0; 0|];
  [|0; 0; 0; 0|]
|] ;;

let sud4 = [|
  [|1; 0; 2; 0|];
  [|0; 0; 0; 0|];
  [|3; 0; 0; 4|];
  [|0; 0; 0; 0|]
|] ;;

let sud4_false = [|
  [|1; 0; 2; 0|];
  [|0; 0; 0; 0|];
  [|3; 0; 0; 4|];
  [|0; 4; 0; 0|]
|] ;;

let sud4_false2 = [|
  [|1; 3; 2; 0|];
  [|0; 0; 0; 0|];
  [|3; 0; 0; 4|];
  [|0; 0; 0; 0|]
|] ;;

let sud4_3sol = [|
  [|1; 2; 3; 0|];
  [|3; 0; 0; 0|];
  [|2; 0; 4; 0|];
  [|0; 0; 0; 0|]
|] ;;

let sud4_2sol = [|
  [|1; 2; 3; 0|];
  [|3; 0; 0; 0|];
  [|2; 1; 0; 0|];
  [|0; 0; 0; 0|]
|] ;;

let sud4_plein = [|
  [|1; 4; 2; 3|];
  [|2; 3; 4; 1|];
  [|3; 2; 1; 4|];
  [|4; 1; 3; 2|]
|] ;;

let sud4_vide = [|
  [|0; 0; 0; 0|];
  [|0; 0; 0; 0|];
  [|0; 0; 0; 0|];
  [|0; 0; 0; 0|]
|] ;;



let sud9_easy = [|
  [|6;0;1;0;9;4;0;0;0|];
  [|0;7;5;0;1;0;6;0;0|];
  [|9;4;8;0;2;7;5;0;0|];
  [|8;2;0;0;7;5;4;0;0|];
  [|0;0;9;0;0;0;0;5;3|];
  [|0;0;4;0;0;0;2;0;8|];
  [|0;0;0;0;0;1;9;6;2|];
  [|4;0;2;0;3;0;1;0;5|];
  [|0;0;0;9;8;2;3;0;0|]
|];;

let sudoku9_facile =  [|
  [|4; 8; 9; 5; 0; 1; 0; 2; 0 |];
  [|7; 5; 0; 0; 0; 0; 8; 1; 0 |];
  [|0; 0; 0; 0; 2; 0; 5; 9; 4 |];
  [|0; 0; 8; 0; 9; 0; 0; 7; 5 |];
  [|5; 0; 0; 0; 0; 8; 0; 0; 0 |];
  [|0; 0; 1; 0; 0; 3; 0; 0; 0 |];
  [|1; 6; 0; 3; 7; 4; 0; 0; 2 |];
  [|0; 0; 0; 0; 0; 5; 7; 3; 6 |];
  [|0; 0; 3; 0; 6; 2; 0; 0; 0 |];
|] ;;

let sud9_17 = [|
  [|0; 0; 0; 0; 4; 2; 0; 0; 0|];
  [|6; 0; 0; 0; 0; 0; 0; 7; 0|];
  [|5; 0; 0; 0; 0; 0; 0; 0; 0|];
  [|0; 0; 0; 0; 0; 0; 0; 6; 0|];
  [|0; 1; 0; 0; 9; 0; 0; 0; 0|];
  [|7; 0; 0; 3; 0; 0; 0; 0; 5|];
  [|0; 2; 9; 0; 0; 0; 4; 0; 0|];
  [|0; 0; 0; 5; 0; 0; 1; 0; 0|];
  [|0; 4; 0; 0; 0; 0; 0; 0; 0|];
|];;

let sud9_Herzberg = [|           (* figure 2 référence [6] *)
  [|0; 0; 0; 0; 0; 0; 0; 1; 0|];
  [|4; 0; 0; 0; 0; 0; 0; 0; 0|];
  [|0; 2; 0; 0; 0; 0; 0; 0; 0|];
  [|0; 0; 0; 0; 5; 0; 4; 0; 7|];
  [|0; 0; 8; 0; 0; 0; 3; 0; 0|];
  [|0; 0; 1; 0; 9; 0; 0; 0; 0|];
  [|3; 0; 0; 4; 0; 0; 2; 0; 0|];
  [|0; 5; 0; 1; 0; 0; 0; 0; 0|];
  [|0; 0; 0; 8; 0; 6; 0; 0; 0|];
|];;

let sud9_Davis1 = [|              (* figure à gauche 24 référence [8]*)
  [|0; 0; 0; 0; 0; 6; 1; 0; 0|];
  [|0; 0; 0; 0; 9; 1; 6; 0; 8|];
  [|7; 0; 0; 0; 0; 0; 0; 0; 0|];
  [|0; 0; 0; 0; 0; 0; 0; 0; 2|];
  [|3; 7; 0; 0; 0; 0; 0; 0; 0|];
  [|0; 0; 0; 0; 0; 4; 0; 0; 6|];
  [|0; 0; 0; 7; 3; 0; 0; 0; 0|];
  [|0; 8; 1; 0; 0; 0; 0; 0; 0|];
  [|0; 0; 0; 5; 0; 0; 0; 0; 0|];
|];;

let sud9_Davis2 = [|              (* figure 24 à droite référence [8]*)
  [|0; 0; 8; 0; 0; 0; 0; 3; 2|];
  [|0; 0; 0; 0; 6; 1; 0; 0; 0|];
  [|0; 0; 5; 0; 0; 0; 0; 0; 0|];
  [|6; 0; 0; 0; 0; 3; 0; 0; 0|];
  [|1; 0; 0; 0; 0; 0; 0; 0; 7|];
  [|0; 0; 0; 2; 0; 0; 0; 0; 8|];
  [|0; 0; 0; 0; 0; 0; 6; 0; 0|];
  [|0; 0; 0; 8; 2; 0; 0; 0; 0|];
  [|5; 3; 0; 0; 0; 0; 9; 0; 0|];
|];;



let sud16_med = [|
  [| 12;0;13;8;6;9;0;16;7;0;10;11;5;14;0;15 |];
  [| 5;11;10;2;0;4;0;13;1;0;6;0;16;3;8;12 |];
  [| 16;14;0;0;12;0;5;0;0;13;0;8;0;0;6;10 |];
  [| 0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0 |];
  [| 7;9;0;0;3;6;16;0;0;15;13;4;0;0;5;14 |];
  [| 13;0;8;4;0;5;0;0;0;0;7;0;15;16;0;1 |];
  [| 14;16;0;3;0;0;0;0;0;0;0;0;10;0;11;2 |];
  [| 0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0 |];
  [| 0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0 |];
  [| 11;7;0;9;0;0;0;0;0;0;0;0;6;0;1;3 |];
  [| 3;0;16;13;0;10;0;0;0;0;1;0;12;11;0;9 |];
  [| 4;6;0;0;14;15;1;0;0;9;12;5;0;0;16;8 |];
  [| 0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0 |];
  [| 1;8;0;0;15;0;3;0;0;16;0;13;0;0;12;6 |];
  [| 6;3;7;5;0;13;0;14;9;0;2;0;11;15;10;16 |];
  [| 10;0;4;16;8;11;0;6;5;0;3;15;9;13;0;7 |];
|] ;;

let sud16_expert = [|
  [| 0;10;13;3;0;16;14;15;0;0;11;0;0;0;0;7 |];
  [| 0;0;0;8;0;0;10;0;1;0;0;0;4;5;16;0 |];
  [| 14;0;0;0;0;6;7;0;0;0;15;0;0;0;10;0 |];
  [| 0;0;0;0;0;9;0;2;0;0;7;10;0;13;0;6 |];
  [| 15;0;2;10;0;0;0;0;0;0;0;0;0;0;0;0 |];
  [| 0;3;6;14;0;0;16;0;0;11;0;0;0;4;0;8 |];
  [| 4;5;0;0;14;0;1;0;6;15;0;0;0;0;0;16 |];
  [| 13;0;0;0;0;3;15;0;4;9;0;16;0;1;5;0 |];
  [| 5;0;0;0;6;0;0;0;3;0;8;0;15;0;4;1 |];
  [| 0;0;7;0;13;0;9;11;14;4;0;0;0;0;8;0 |];
  [| 0;8;0;0;4;10;0;0;12;0;6;0;0;0;0;0 |];
  [| 11;15;0;6;0;0;0;0;0;13;9;0;12;0;7;0 |];
  [| 2;0;0;0;0;1;0;12;0;0;5;0;0;0;14;0 |];
  [| 0;0;0;0;5;2;11;0;0;0;4;3;0;0;0;9 |];
  [| 0;4;9;0;0;0;8;14;0;0;0;7;0;3;0;0 |];
  [| 0;0;5;0;0;0;0;0;9;1;13;0;0;0;0;10 |];
|] ;;

(* sudoku 25x25 entièrement résoluble par propagation *)
let s25_0 = [|               
  [|  19; 0; 7; 0;10;  0;16; 8; 1;25;  9;24; 3; 0; 2;  0;15; 4; 0;22;  0; 0;20; 6; 0|];
  [| 13; 1;20; 5; 0;  3; 0; 9;22;19;  4; 0; 0;12;21; 10; 0; 0; 0; 0;  11; 0;16; 0; 7|];
  [|  9;18; 0; 3; 2; 21;15; 0; 0; 0; 10;14; 1;19; 0;  8; 0; 0;20;12;  25; 5; 0;22; 4|];
  [|  0; 8;25; 4;21;  0; 0;24; 0;10;  0; 0; 0;20; 5;  2; 0; 0; 3;16;  18;15; 0; 9;19|];
  [|  0; 0; 0; 0; 0;  0; 0; 0; 0; 0;  0; 0; 0; 0; 0;  0; 0; 0; 0; 0;   0; 0; 0; 0; 0|];
  [|  4;20; 1; 0; 0;  0; 0; 0; 0; 0; 0;  0; 0; 0; 0;  0; 0; 0; 0; 0;   0; 0; 0; 0; 0|];
  [| 14; 9; 5;15;16; 18; 0; 0;12; 3;  0;22; 7; 2; 4; 19; 8; 1;25; 0;   0; 0; 0;10; 6|];
  [|  0;21;23;18; 6;  2;10; 0;20; 0; 16; 0; 9; 8; 0; 14; 3;22; 0;15;  24; 0; 4; 0; 5|];
  [|  0; 3; 0;10; 0;  6; 5; 4; 0; 9; 19;20; 0;15;14;  0; 7;24;11;18;   0;16; 0; 1; 0|];
  [| 11;19; 0; 0; 8; 22; 0;16; 7; 1; 25;10; 0; 5;18;  0; 4; 6;12;21;  14;20; 0; 0; 0|];
  [| 21; 0; 0; 0; 0;  7; 0; 0; 0; 0;  0; 0; 0; 0; 0;  0; 0; 0; 0; 0;  20; 2;13; 0; 0|];
  [|  8;10; 0; 7; 0; 20;18; 0; 3;15;  0; 4;12;11; 9; 25;19; 0; 0; 0;   1;14; 0; 0; 0|];
  [|  0;12; 0; 9; 3; 14; 1;19; 0; 6; 15;25;20; 0;24; 22; 0;18;10; 0;   0; 8; 0; 5; 0|];
  [| 24;16; 0;25;20; 12; 9; 0;10; 5; 18;21; 6; 0; 7;  3; 2;11; 0;14;   0; 0;22;19; 0|];
  [|  0;15; 4;19;14; 25;22;11;24; 0;  5; 0; 8; 0;16;  0;21; 0; 7; 0;   0; 9; 0;17;12|];
  [|  2;24;21; 0;12;  4;19; 6; 0;22;  7; 0;25; 9;20;  1;10; 8; 0; 0;  5; 0; 3; 0; 0|];
  [| 10; 0; 0;14; 4;  8;20; 0;18; 0;  0; 6; 0; 0;22;  9;12;16; 0; 5;  0; 0; 2;15;25|];
  [|  0; 0; 0; 6; 9;  0; 0; 0;25; 7; 21;12; 0; 0; 0;  0; 0; 0; 0; 0;  0; 10;18;0; 0|];
  [|  0;25; 0; 0;18; 24; 3; 0;17; 0; 14;15; 2; 0; 8;  7; 0; 0; 0; 0;  0; 0;12; 0; 0|];
  [|  0; 0; 0;22;15;  9; 0; 0; 2;12;  1; 5;10; 0;19;  0; 0; 3;24;25;  6; 0;21; 4; 8|];
  [|  15; 2; 0;13; 0;  0; 0;20;14;18; 22;16; 5; 3; 0; 12;25;10; 0; 0;  8; 4;11; 0; 0|];
  [|  12;22; 9; 0; 0; 15; 0; 0; 0;24; 20; 8;18;10; 0;  4; 0; 7; 0; 0;  2; 0; 0;16; 0|];
  [|  0; 4; 0;24; 7;  0; 6; 0; 9;16;  0; 1; 0; 0; 0;  0; 0; 0; 0; 0;   0; 0; 0; 0; 0|];
  [|  0; 6;10; 0; 1;  0; 8; 0; 5; 4;  2; 9; 0;25;12; 20;  0; 0;18;24; 15;21;19; 0; 3|];
  [|  20; 5;18; 8;19;  1; 0;21; 0; 2; 24;17; 0; 0; 0;  0; 0; 0; 0; 0;  0; 0; 0; 0;10|];
|];;

(* trouvé sur https://sudokugeant.cabanova.com/files/downloads/g16_198.pdf *)
let s25_G198 = [|
      [|  0; 0; 0; 0; 0;  0; 0; 0; 0; 0;  0;23; 0;15; 0;  0; 0; 0; 0; 0;  0; 0; 0; 0; 0 |];
      [|  0; 0; 0; 0; 0;  0; 0; 0; 9; 3;  0; 0;21; 0; 0;  1;15; 0; 0; 0;  0; 0; 0; 0; 0 |];
      [|  0; 0; 7; 0;13; 24;12;17; 0;15;  8; 0;19; 0;10; 14; 0; 6;21;20;  1; 0;22; 0; 0 |];
      [|  0; 0; 0;11;17; 25; 6;21; 2; 0;  9;13; 5;14;12;  0;19;16;10; 8; 15; 3; 0; 0; 0 |];
      [|  0; 0; 9;14;12; 10; 4; 1;16; 0; 18; 6; 0;24;17;  0;25; 3; 5;23; 21;13;20; 0; 0 |]; 
      [|  0; 0;22;20;21;  0; 0;16; 0; 0; 17; 0; 0; 0; 8;  0; 0; 7; 0; 0; 23;18;19; 0; 0 |];
      [|  0; 0; 8; 9;18;  0; 0; 0;15; 6; 19; 4; 0;21;25; 16;12; 0; 0; 0; 13;20; 5; 0; 0 |];
      [|  0; 0;25; 5;15; 18; 0; 0; 1;13;  0;12; 0;10; 0;  9; 6; 0; 0;24; 11; 7; 8; 0; 0 |];
      [|  0;11; 0; 4; 1;  0; 2;14;12;10; 13; 0;18; 0; 5; 23; 8;17;19; 0; 24;22; 0;25; 0 |];
      [|  0;10;13; 0; 0;  0;25;23; 4; 8; 20; 9; 2;11;24; 15; 1;18;22; 0;  0; 0;21;17; 0 |];
      [|  0; 0;23;17; 6; 12; 3; 0;21;20;  0;22; 0;25; 0;  8;13; 0; 7;15; 18;24; 2; 0; 0 |];
      [| 13; 0; 0;24; 2;  0;22;25; 0;18; 15; 0; 6; 0; 1; 21; 0;10; 4; 0; 17;23; 0; 0;12 |];
      [|  0;25;18; 8; 0;  0; 0; 0; 6;16;  0;11; 0;20; 0;  3;24; 0; 0; 0;  0;15;10;22; 0 |];
      [| 14; 0; 0;10;20;  0;15; 9; 0; 4;  5; 0; 3; 0;13; 12; 0; 2; 1; 0; 19; 8; 0; 0;21 |]; 
      [|  0; 0;15; 1;22; 11; 5; 0;10; 7;  0;16; 0;17; 0; 19;18; 0;14; 6; 20; 4; 9; 0; 0 |];
      [|  0;14; 3; 0; 0;  0; 7; 5;24; 9; 12; 1;17;19; 6; 20;23; 4; 8; 0;  0; 0;11;15; 0 |];
      [|  0; 4; 0;23;11;  0;14;15;18; 2;  3; 0;10; 0; 9; 13;21; 1;12; 0; 16;17; 0;20; 0 |];
      [|  0; 0;19;22; 5; 16; 0; 0;20; 1;  0;15; 0; 7; 0; 17; 9; 0; 0; 3;  4; 2;13; 0; 0 |];
      [|  0; 0;24; 7;10;  0; 0; 0;17;23; 25;14; 0; 8; 2; 18; 5; 0; 0; 0;  9;12; 6; 0; 0 |];
      [|  0; 0;21;15; 9;  0; 0;12; 0; 0;  4; 0; 0; 0;11;  0; 0;22; 0; 0;  7; 1;23; 0; 0 |];
      [|  0; 0; 1; 2; 7;  4; 8;11;13; 0; 24;21; 0;23; 3;  0;17;19;20; 9;  5;16;14; 0; 0 |];
      [|  0; 0; 0; 3;19;  2;16;10;25; 0;  6; 8;11;13;15;  0; 7;24;18;22; 12;21; 0; 0; 0 |];
      [|  0; 0; 4; 0;25;  1;23; 7; 0;21; 16; 0;20; 0;19; 10; 0; 8;15;12;  2; 0; 3; 0; 0 |];
      [|  0; 0; 0; 0; 0;  0; 0; 0;14;17;  0; 0; 4; 0; 0; 11; 3; 0; 0; 0;  0; 0; 0; 0; 0 |];
      [|  0; 0; 0; 0; 0;  0; 0; 0; 0; 0;  0;10; 0;12; 0;  0; 0; 0; 0; 0;  0; 0; 0; 0; 0 |];
    |];;









(*****************************************************)
(* TESTS *)

let test_unique empty (nom,g) =  (*empty = f° qui prend rank et retourne puzzle vide*)
  Printf.printf "==> sudoku %s\n" nom ;
  imprime g; print_newline(); 
  Gc.compact(); (* empêcher que l'effacement de données inutiles rajoute du temps d'éxécution *)
  let ti = Sys.time() in  (*heure du système avant début*)
  let p=import empty g in
  let q=cherche_2prem p in
  (try
     let r=solver_param q in
     assert (r=1) ;
   with
     Failure "trop long" -> Printf.printf "Echec car trop long!\n");
  let tf=Sys.time() in   (*heure du système à la fin*)
  Printf.printf "temps de calcul: %f s\n" (tf-.ti) ;
  Printf.printf "nb d'undo : %d\n" q.count_undo ;
  print_newline()
;;

let list_u = [
  ("sud4",sud4); ("sud4_hard",sud4_hard);  ("sud4_plein",sud4_plein); 
  ("sudoku9_facile",sudoku9_facile); ("sud9_easy",sud9_easy); ("sud9_Herzberg",sud9_Herzberg); ("sud9_Davis1",sud9_Davis1); ("sud9_Davis2",sud9_Davis2); ("sud9_17",sud9_17);
  ("sud16_expert",sud16_expert); ("sud16_med",sud16_med); ("s25_0",s25_0); ("s25_G198",s25_G198);
];;


let test_1sol empty (nom,g) =  (*empty = f° qui prend rank et retourne puzzle vide*)
  Printf.printf "==> sudoku %s\n" nom ;
  imprime g; print_newline(); 
  Gc.compact(); (* empêcher que l'effacement de données inutiles rajoute du temps d'éxécution *)
  let ti = Sys.time() in  (*heure du système avant début*)
  let p=import empty g in
  let q=collecte_1 p in
  (try
     let r=solver_param q in
     match r with
     |None -> failwith "1 solution attendue, 0 trouvée"
     |Some s -> imprime s ; print_newline() ;
   with
     Failure "trop long" -> Printf.printf "Echec car trop long!\n");
  let tf=Sys.time() in   (*heure du système à la fin*)
  Printf.printf "temps de calcul: %f s\n" (tf-.ti) ;
  Printf.printf "nb d'undo : %d\n" q.count_undo ;
  print_newline()
;;


let test_nbsol empty (nom,g,n) =
  Printf.printf "==> sudoku %s,(nbsol=%d)\n" nom n;
  imprime g; print_newline(); 
  (try
     let p=import empty g in
     let q=nb_sols p in
     assert (solver_param q=n);
     Printf.printf "nb d'undo : %d\n" q.count_undo ;
   with
     Failure "grille incorrecte" -> assert (n=0));
  print_newline()
;;

let list_nb = [
  ("sud4_vide",sud4_vide,288); ("sud4_2sol",sud4_2sol,2); ("sud4_3sol",sud4_3sol,3); ("sud4_false",sud4_false,0)
];;



let test empty =
  List.iter (test_nbsol (empty true)) list_nb;
  Printf.printf "==> test_nbsol OK\n"; print_newline() ;
  List.iter (test_unique (empty true)) list_u;
  Printf.printf "==> test_unique OK\n"; print_newline()
;;

let mesure empty =
  List.iter (test_1sol (empty false)) list_u;
  Printf.printf "==> mesure OK\n"; print_newline()
;;

print_newline();;
Printf.printf "############################## test avec propagation \n" ;;
test p_empty ;;

print_newline();;
print_newline();;
Printf.printf "############################## test avec insertion à coût constant \n" ;;
test b_empty;;


print_newline();;
Printf.printf "############################## mesure avec propagation \n" ;;
mesure p_empty ;;

print_newline();;
print_newline();;
Printf.printf "############################## mesure avec insertion à coût constant \n" ;;
mesure b_empty;;
