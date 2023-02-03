#load "graphics.cma";;
open Graphics;;
open_graph ":0";;
resize_window 800 800;;

(* Couleurs *) 
let noir = rgb 0 0 0;;
let blanc = rgb 250 250 250;;
let bleu = rgb 69 150 239;;
let noir_contour = rgb 13 1 3;;
let rouge = rgb 224 8 3;;
let vert = rgb 69 139 55;;
let violet = rgb 69 67 150;;
let mauve = rgb 115 8 241;;

(* Exceptions *)
exception Stop;;

(* Types *)
type direction = Ouest | Est | Nord | Sud | Null;;
type sortie = SortieNord | SortieEst | SortieOuest | SortieSud | SortieNull;;
type coords = {x0:float; y0:float};;
type vecteur = {vx:float; vy:float};;
type personne = {mutable x:float; mutable y:float; mutable v:float; mutable etage:int; mutable sortie:int};;

(* Variables Globales *)
let coord_SortieNord = (400., 800.);;
let coord_SortieEst = (800., 400.);;
let coord_SortieSud = (400., 0.);;
let coord_SortieOuest = (0., 400.);;

let csteRayon = 10.;;
let taux_hasard = 10;; (* taux de panique *)
let score = ref 0;;

			(* ~~~~~ Fonctions ~~~~~ *)

(* Page d'accueil *)
let page_accueil () = 
	begin 
	set_color violet;
	fill_rect 0 0 800 800;
	
	set_color noir;
	moveto 15 30;
	set_text_size 15;
	draw_string "Made by Elisa";
	
	moveto 75 500;
	set_text_size 30;
	draw_string "Simulation d'évacuation d'urgence";
	
	moveto 75 400;
	set_text_size 25;
	draw_string "Commandes :";
	
	moveto 60 350;
	set_text_size 20;
	draw_string "- Appuyez sur un chiffre k pour observer l'avancement de l'évacuation";
	moveto 60 325;
	draw_string "dans l'étage k";
	moveto 60 300;
	draw_string "- Appuyez sur espace pour démarrer la simulation";
	end;;


let initialisation_etage () = 
	begin
	(* background *)
	set_color bleu;
	fill_rect 0 0 800 800;
	
	set_color blanc;
	fill_rect 350 0 100 800;
	fill_rect 0 350 800 100;

	end;;

	(* ~~~~~ Fonctions de conversion ~~~~~ *)
let conversion_sorties n = match n with 
	| 1 -> SortieNord
	| 2 -> SortieOuest 
	| 3 -> SortieEst
	| 4 -> SortieSud
	| _ -> SortieNull;;

let coord_of_direction direction = match direction with 
	| Ouest -> (-1, 0)
	| Est -> (1, 0)
	| Nord -> (0, 1)
	| Sud -> (0, -1)
	| _ -> (0, 0);;

let conversion_clavier t = match t with 
	| ' ' -> -1
	| k -> (int_of_char k)-48;;
	
let coordonnees_sorties s = match s with
	| SortieNord -> coord_SortieNord
	| SortieEst -> coord_SortieEst
	| SortieOuest -> coord_SortieOuest
	| SortieSud -> coord_SortieSud
	| _ -> (0., 0.);;

let radian_of_degre deg = 
	(deg *. Float.pi) /. 180.;;
	
let coords_dans_le_tableau x y = (* x = p*ecart + r *) (* à revérifier *)
	let ecart = 800/(800/(2*(int_of_float csteRayon))) in
	let i = (int_of_float x - (int_of_float x mod ecart))/ecart
	and j = (int_of_float y - (int_of_float y mod ecart))/ecart
	in (i, j);;

let coord_of_stops direction = match direction with 
|Ouest -> (175., 400.)
|Est -> (625., 400.)
|Nord -> (400., 625.)
|Sud -> (400., 175.)
|_ -> raise Stop;;

let points_stop x y = 
	if x < 175. then coord_of_stops Ouest
	else if x > 625. then coord_of_stops Est
	else if y > 625. then coord_of_stops Nord
	else if y < 175. then coord_of_stops Sud
	else (400., 400.);;
	
		(* ~~~~~ Fonctions de calcul ~~~~~ *)
let norme vect = sqrt(vect.vx**2. +. vect.vy**2.);;

let distance x1 y1 x2 y2 = sqrt((x1 -. x2) ** 2. +. (y1 -. y2)**2.);;

let normaliser v = 
	let n = norme v in 
	{vx = v.vx/.n; vy = v.vy/.n};;

let abs x = if x < 0. then -.x else x;;

let rotation angle x y = (* angle en degré *)
	let a = radian_of_degre angle in 
	let x2 = (x *. cos a -. y *. sin a)
	and y2 = (x *. sin a +. y *. cos a) in 
	if abs x2 < 1e-10 then 
		if abs y2 < 1e-10 then (0., 0.)
		else (0., y2)
	else 
		if abs y2 < 1e-10 then (x2, 0.)
		else (x2, y2);;
		
let projection vx vy axe = match axe with 
| "abs" -> (vx, 0.)
| "ord" -> (0., vy)
| _ -> raise Stop;;

		(* ~~~~~ Fonction de collision ~~~~~  *)
let collision x1 y1 x2 y2 = (* collision entre deux personnes *)
	(distance x1 y1 x2 y2) < 2.*.csteRayon;;

let rec collision_point_liste p l = match l with (* collision entre une personne et une liste de personnes*)
	| [] -> false
	| t::q -> if p <> t then collision p.x p.y t.x t.y || collision_point_liste p q
						else collision_point_liste p q;;

		(* ~~~~~ Fonctions de vérification ~~~~~ *)
let arrivee p = (* vérifie si la personne est arrivée à sa sortie définie *)
	let s = p.sortie in 
	let (a, b) = coordonnees_sorties (conversion_sorties s) in
	p.x = a && p.y = b ;;

let rec arrivee_liste l = match l with (* vérifie si toutes les personnes de la liste sont arrivés *)
 	| [] -> true
 	| t::q -> arrivee t && arrivee_liste q;;
 	
let rec arrivee_etage etage = 
	let a = ref false in
	let n = Array.length etage in
	for i = 0 to n-1 do
		for j = 0 to n-1 do
		a := !a || arrivee_liste etage.(i).(j);
		done
	done; !a;;		
	
let arrivee_liste l = l = [];; (* à vérifier si c'est correct *)

let arrivee_etage etage = 
	let a = ref false in 
	let n = Array.length etage in
	for i = 0 to n-1 do
		for j = 0 to n-1 do
			a := !a || etage.(i).(j) = [] 
		done;
	done;
	!a;;
			 
let bords x y = if (350. < x) && (x < 450.) then false (* renvoie true si les coordonnées sont sur les bords/à l'intérieur *)
		else not ((350. < y) && (y < 450.));;

let hors_du_plateau x y = x < 0. || x > 800. || y < 0. || y > 800.;;

		(* ~~~~~ Fonctions de génération ~~~~~ *)
let tableau_etage () = (* crée le tableau stockant les personnes *)
	Array.make_matrix (800/(2*(int_of_float csteRayon))) (800/(2*int_of_float(csteRayon))) [];;

let genere_coords () = (* renvoie des coordonnées situées dans le couloir *)
	let x = float_of_int(Random.int (800 - 2*int_of_float(csteRayon))) +. csteRayon in
	if 350. < x && x < 450. 
		then (x, float_of_int(Random.int (800 - 2*int_of_float(csteRayon))) +. csteRayon)
	else (x, float_of_int(Random.int (100 - 2*int_of_float(csteRayon))) +. csteRayon +. 350.) ;;

let genere_sortie () = (Random.int 4) + 1;;

let genere_vitesse () = (Random.float 2.) +. 1.;; (* vitesse entre 0 et 3 *)

let plus_ou_moins () = if (Random.int 2) = 1 then 1. else -1.;;

let genere_personne x y v etage sortie = (* génère une personne *)
	{x = x; y = y; v = v; etage = etage; sortie = sortie};;
	
let genere_personne_collisions liste etage = (* à supp *)
	let s = genere_sortie () in
	let v = genere_vitesse () in
		let rec boucle () = 
			let (x, y) = genere_coords () in
			let p = genere_personne x y v etage s in
				if not (collision_point_liste p liste) then p
				else boucle ()
	in boucle ();;	

let genere_etage nombre etage = (* a supp *)
	let rec genere_etage_aux n liste = 
		if n = 0 then liste 
		else 
			let p = genere_personne_collisions liste etage in
			genere_etage_aux (n-1) (p::liste)
	in genere_etage_aux nombre [];;

let genere_personne_collisions etage numeroEtage = (* génère une personne en prenant en compte les collisions*)
	let s = genere_sortie () in
	let v = genere_vitesse () in
	let rec boucle () = 
		let (x, y) = genere_coords () in
		let p = genere_personne x y v numeroEtage s in
		let (i, j) = coords_dans_le_tableau p.x p.y in
		if collision_point_liste p etage.(i).(j)
			then boucle ()
		else p
	in boucle();;
	
let genere_etage nombrePersonne numeroEtage = (* génère un étage*)
	let etage = tableau_etage() in
	for k = 0 to nombrePersonne-1 do
		let p = genere_personne_collisions etage numeroEtage in 
		let (i, j) = coords_dans_le_tableau p.x p.y in
		etage.(i).(j) <- p::etage.(i).(j)
	done;
	etage;;
	
let genere_immeuble nombrePersonne nombreEtage = (* génère l'immeuble *)
	let immeuble = ref [] in 
	for i = 0 to nombreEtage-1 do
		immeuble := (genere_etage nombrePersonne i)::!immeuble
	done;
	List.rev !immeuble;;

		(* ~~~~~ Fonctions d'affichage ~~~~~ *)
let affiche_personne p = (* affiche une personne*)
	begin
	set_color rouge;
	fill_circle (int_of_float(p.x)) (int_of_float(p.y)) (int_of_float csteRayon);
	end;;

let rec affiche_personnes l = match l with (* affiche une liste de personne *)
	| [] -> ()
	| t::q -> begin affiche_personne t; affiche_personnes q end;;

let supprime_personne p = (* supprime une personne *)
	begin
	set_color blanc;
	fill_circle (int_of_float(p.x)) (int_of_float(p.y)) (int_of_float csteRayon);
	end;;

let rec supprime_personnes l = match l with (* supprime une liste de personne *)
	| [] -> ()
	| t::q -> begin supprime_personne t; supprime_personnes q end;;

let affiche_etage etage = (* affiche etage + emplacement des personnes*)
	let n = Array.length etage in
	begin
	initialisation_etage ();
	for i = 0 to n-1 do
		for j = 0 to n-1 do
			affiche_personnes etage.(i).(j)
		done
	done;
	initialise_score();
	actualise_score ();
	end;; 

let supprime_score () = 
	set_color bleu;
	fill_rect 90 15 50 15;;

let initialise_score () = 
	begin
	set_color noir;
	moveto 15 15;
	set_text_size 15;
	draw_string "Score : ";
	end;;

let actualise_score () = 
	begin
	set_color noir;
	moveto 90 15;
	set_text_size 15;
	draw_string (string_of_int !score);
	end;;


		(* ~~~~~ Fonctions de déplacement ~~~~~ *)   
let ponderation p vx vy = match p.sortie with 
|1 |4 -> if 350. < p.x && p.x > 450. then projection vx vy "ord" else projection vx vy "abs"
|2 |3 -> if 350. < p.y && p.y > 450. then projection vx vy "abs" else projection vx vy "ord"
|_ -> raise Stop;;

let angles = 
	let a = Array.make 7 0. in 
	let j = ref 1 in
	for i = 1 to 3 do
		begin
		a.(!j) <- 45. *. float_of_int i;
		a.(!j + 1) <- -. a.(!j);
		j := !j + 2;
		end
	done; a;;

let nouvelle_direction_collision p vect l = (* analyse les possibilités de déplacement *)
	let vx2 = ref vect.vx
	and vy2 = ref vect.vy
	and i = ref 0 in
	while ((collision_point_liste {x = p.x +. !vx2; y = p.y +. !vy2; v = p.v; etage = 0; sortie = 0} l 
	|| (bords (p.x +. !vx2) (p.y +. !vy2))||hors_du_plateau (p.x +. !vx2) (p.y +. !vy2))
	&& !i < Array.length angles) do
		let (c, d) = rotation (angles.(!i)) vect.vy vect.vy in 
			begin
			incr i;
			vx2 := c;
			vy2 := d;
			end;
	done; 
	if !i = Array.length angles then (0., 0.)
	else (!vx2, !vy2);;

(*

let rec nouvelle_direction_collision2 p vect l = (* renvoie le nouveau vecteur *)
	if not (collision_point_liste {x = p.x +. vect.vx; y = p.y +. vect.vy; etage = p.etage; sortie = p.sortie} l) 
	&& not (hors_du_plateau (p.y +. vect.vy) (p.y +. vect.vy)) && (not (bords (p.x +. vect.vx) (p.y +. vect.vy)))
	then vect.vx, vect.vy (* déplacement valide/possible *)
	else let angles = angles() in 
	let rec aux v i = 
		let vx, vy = v in 
			if i < 7 then
				if hors_du_plateau (p.x +. vx) (p.y +. vy) || collision_point_liste {x = p.x +. vect.vx; y = p.y +. vect.vy; etage = p.etage; sortie = p.sortie} l 
				then aux (rotation angles.(i) vect.vx vect.vy) (i+1)
				else if bords (p.x +. vx) (p.y +. vy) 
						 then let vx, vy = (ponderation p vx vy) in nouvelle_direction_collision p {vx = vx; vy = vy} l
						 else (vx, vy)
			else (0., 0.)
	in aux (vect.vx, vect.vy) 1;;
*)
		
let deplacement_sans_hasard p vect l = (* modifie les coordonnées d'une personne selon son vecteur déplacement *)
	let vx, vy = nouvelle_direction_collision p vect l in
	begin
		p.x <- p.x +. vx;
		p.y <- p.y +. vy;
	end;;

let rec deplacement_avec_hasard p vect l = (* fonction améliorée qui prend en paramètre un facteur hasard *)
	let a = Random.float 180. in 
	let vx, vy = rotation a vect.vx vect.vy in 
	if (not (collision_point_liste {x = vx; y = vy; v = 0.; etage = 0; sortie = 0} l) && 
	(not (bords (p.x +. vx) (p.y +. vy)))) then
		begin 
		p.x <- p.x +. vx;
		p.y <- p.y +. vy;
		end
	else deplacement_avec_hasard p vect l;;

(* il faut complexifier cette fonction : les points se tassent sur les côtés en créant des amas *)
let vecteur_deplacement p = (* renvoie le vecteur déplacement d'une personne *)
	let x_s, y_s = coordonnees_sorties (conversion_sorties (p.sortie)) in
	if distance p.x p.y x_s y_s <= 500. then (* si la personne est proche de sa sortie attribuée *)
		let v = normaliser {vx = x_s -. p.x; vy = y_s -. p.y}
		in {vx = v.vx*.p.v; vy = v.vy*.p.v}
	else 
		let x_p, y_p = points_stop p.x p.y in (* disjonction de cas si la personne est plus ou moins loin de sa sortie *)
		let v = normaliser {vx = x_p -. p.x; vy = y_p -. p.y} 
		in {vx = v.vx*.p.v; vy = v.vy*.p.v}
 ;;
		
let pop liste element = 
	let b = ref true in 
	let rec aux compteur l1 l2 = match l1 with 
	|[] -> List.rev l2
	|t::q -> if t = element && !b
						then begin b := false; aux (compteur + 1) q l2 end
						else aux (compteur + 1) q (t::l2)
	in aux 0 liste [];;

let applique_deplacement_personne p tableau l = (* applique le déplacement d'une personne *)
	let x_s, y_s = coordonnees_sorties (conversion_sorties (p.sortie)) in
	let tirage = Random.int 100 in 
		if distance p.x p.y x_s y_s >= csteRayon then
			if tirage < taux_hasard then deplacement_avec_hasard p (vecteur_deplacement p) l
			else deplacement_sans_hasard p (vecteur_deplacement p) l
		else (* cas où la personne est à côté de la sortie *)
			let (i, j) = coords_dans_le_tableau p.x p.y in
			begin
			p.x <- x_s;
			p.y <- y_s;
			tableau.(i).(j) <- pop tableau.(i).(j) p;
			incr score;
			end;;

(* à supp *)
let applique_deplacement_liste etage i j = (* applique le déplacement d'une liste de personne*)
	let rec aux deplacements_faits l = match l with 
	| [] -> ()
	| t::q -> begin applique_deplacement_personne t etage deplacements_faits; 
									aux (t::deplacements_faits) q 
						end
	in aux [] etage.(i).(j);;
	
let rec applique_deplacement_liste etage i j = 
	let rec aux l = match l with
	| [] -> ()
	| t::q -> begin 
						applique_deplacement_personne t etage etage.(i).(j); 
						aux q;
						end
					
	in aux etage.(i).(j);;

let applique_deplacement_etage etage = 
	for i = 0 to Array.length etage - 1 do
		for j = 0 to Array.length etage - 1 do
			applique_deplacement_liste etage i j;
		
		done
	done;;

	(* ~~~~~ Fonction main ~~~~~ *)
let main () = 
	let evacuants = genere_immeuble 100 10 in
	let time = ref (Sys.time ()) in
	let continuer = ref true in
	let toucheAppuyee = ref false in
	let touche = ref 'a' in
	let touche_convertie = ref 0 in
		begin
			open_graph ":0";
			resize_window 800 800;
			page_accueil ();
			
			(* page d'accueil *)
			(* affiche par défaut l'étage 0 *)
			while !continuer do
				toucheAppuyee := key_pressed ();
				if !toucheAppuyee then
					touche := read_key ();
					if !touche = ' ' then 
						begin
						affiche_etage (List.nth evacuants 0);
						toucheAppuyee := false;
						continuer := false;
						end
			done;
			continuer := true;
			while !continuer do
				begin
				auto_synchronize false;
				applique_deplacement_etage (List.nth evacuants !touche_convertie);
				toucheAppuyee := key_pressed ();
				if !toucheAppuyee then 
					begin 
					touche := read_key ();
					touche_convertie := conversion_clavier !touche;
					print_int !touche_convertie;
					toucheAppuyee := false;
					end;
					
				if 10 > !touche_convertie && !touche_convertie >= 0 then 
					affiche_etage (List.nth evacuants !touche_convertie);

				
				while Sys.time() -. !time < 0.001 do () done; (* sleep *)
				time := Sys.time();
				if arrivee_etage (List.nth evacuants 0) then continuer := false;
				
				synchronize ();
				end;
			done;
		end;;

main ();;