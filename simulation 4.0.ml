#load "graphics.cma";;
open Graphics;;
open_graph ":0";;
resize_window 800 800;;

(* Couleurs *) 
let noir = rgb 0 0 0;;
let blanc = rgb 250 250 250;;
let bleu = rgb 135 206 250;;
let noir_contour = rgb 13 1 3;;
let rouge = rgb 220 20 60;;
let vert = rgb 69 139 55;;
let violet = rgb 69 67 150;;
let mauve = rgb 115 8 241;;
let gris = rgb 128 128 128;;

(* Exceptions *)
exception Stop;;
exception DirectionTrouvee of float;;

(* Types *)
type vecteur = {vx:float; vy:float};;
type personne = {mutable x:float; mutable y:float; mutable v:float; mutable chemin:int list; mutable tauxPanique:float};;

(* Variables Globales *)
let csteRayon = 8.;;
let nombreEvacues = ref 0;;
let nombreSorties = 3;;
let n = 800/50;; (* nombre de cellules par ligne ou colonne *)
let m = 50;; (* taille de la cellule *)
let coordonneesSommets = 
[| (50., 750.); (400., 750.); (750., 750.); (50., 50.); (400., 50.); (750., 50.) |];;
			
			(* ~~~~~ Structure de graphe ~~~~~ *)
(* 
- Liste d'arêtes
- Liste d'adjacence à privilégier pour Dijsktra
- Matrice d'adjacence
*)

let listeAdj = [| [1; 3], [0; 4; 2], [1; 5], [0; 4], [1; 3; 5], [2; 4] |];;

			(* ~~~~~ Implémentation de la file de priorité ~~~~~ *)

type file_prio_element = {sommet: int; priorite: int};;

type file_prio = file_prio_element list;;

let rec file_prio_ajoute fp element = match fp with
|[] -> List.rev (element::fp) 
|t::q -> if element.priorite >= t.priorite then element::t::q
					else t::(file_prio_ajoute q element)
	;; (* vérifier la correction*)

let file_prio_extrait fp = 
	(List.hd fp, List.tl fp);;

let file_prio_vide fp = List.length fp = 0;;

			(* ~~~~~ Algorithme de Dijkstra à adapter ~~~~~ *)
let dijskstra listeAdj depart arrivee = 
		let predecesseur = Array.make (Array.length listeAdj) (-1)
		and visite = Array.make (Array.length listeAdj) false 
		and fp = [] in
				file_prio_ajoute fp {sommet = depart; priorite = 0};
				for i = 0 to Array.length listeAdj - 1 do
						if i <> depart then filedepriorite_ajoute (i, min_int) fp
				done;
				while not visite.(arrivee) do 
						let (sommet, distance) = file_prio_extrait fp in
								visite.(sommet) <- true;
								if sommet <> arrivee 
								then List.iter (fun (s,d) ->
								if not visite.(s) && filedepriorite_priorite s fp < distance - d
								then begin
										 predecesseur.(s) <- sommet;
										 filedepriorite_augmentepriorite (s, distance-d) fp;
										 end) listeAdj.(sommet)
				done;
				let chemin = ref [arrivee] in 
						while predecesseur.(List.hd !chemin) <> -1 do
								chemin := predecesseur.(List.hd !chemin)::!chemin
						done;
						!chemin;;

			(* ~~~~~ Fonctions ~~~~~ *)
(* Page d'accueil *)
let page_accueil () = 
	begin 
	set_color violet;
	fill_rect 0 0 800 800;
	
	set_color noir;
	moveto 15 30;
	set_text_size 15;
	draw_string "Elisa CHIEN";
	
	moveto 75 500;
	set_text_size 30;
	draw_string "Simulation d'évacuation d'urgence";
	
	set_text_size 22;
	moveto 60 300;
	draw_string "Appuyez sur espace pour démarrer la simulation";
	end;;

let initialisation_etage () = 
	begin
		set_color blanc;
		fill_rect 0 0 800 800;
		set_color gris;
		fill_rect 100 100 250 600;
		fill_rect 450 100 250 600;
		set_color bleu;
		for i = 0 to 2 do
			for j = 0 to 1 do
				fill_rect (i*350) (j*700) 100 100;
			done
		done;
		set_color black;
		for i = 0 to n-1 do
			moveto (i*m) 0;
			lineto (i*m) 800;
		done;
		for i = 0 to n-1 do
			moveto 0 (i*m);
			lineto 800 (i*m);
		done;
		
	end;;

		(* ~~~~~ Fonctions de calcul ~~~~~ *)
let norme vect = sqrt(vect.vx**2. +. vect.vy**2.);;

let distance x1 y1 x2 y2 = sqrt((x1 -. x2) ** 2. +. (y1 -. y2)**2.);;

let normaliser v = 
	let n = norme v in 
	{vx = v.vx/.n; vy = v.vy/.n};;

let abs x = if x < 0. then -.x else x;;

let radian_of_degre deg = 
	(deg *. Float.pi) /. 180.;;

let rotation angle vect = (* angle en degré *)
	let x = vect.vx in
	let y = vect.vy in 
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

let coordonnees x y = (* convertit les coordonnées (x, y) en coordonnées du tableau de l'étage *)
	let x = int_of_float x
	and y = int_of_float y in 
	((x - (x mod m))/m, (y - (y mod m))/m);;
	
let densite etage i j = 
	let nombrePersonnesCellule = List.length etage.(i).(j) in 
	(float_of_int nombrePersonnesCellule)/.(float_of_int (m*m));;
	
let actualise_densite etage densiteEtage = 
	for i = 0 to n-1 do
		for j = 0 to n-1 do
			 densiteEtage.(i).(j) <- densite etage i j
		done
	done;;

		(* ~~~~~ Fonctions de vérification ~~~~~ *)
let dans_le_couloir x y = 
	not (((100. <= x && x <= 350.) || (450. <= x && x <= 700.))
	&& (100. <= y && y <= 700.));;

let arrivee_etage etage = Array.for_all (fun l -> Array.for_all (fun cellule -> List.length cellule = 0) l) etage;;


		(* ~~~~~ Fonction de collision ~~~~~  *)
let collision x1 y1 x2 y2 = (* collision entre deux personnes *)
	(distance x1 y1 x2 y2) < 2.*.csteRayon;;

let collision_dans_cellule i j etage p = (* collision entre une personne et une liste de personnes *)
	List.exists (fun voisin -> if p <> voisin then collision p.x p.y voisin.x voisin.y else false) etage.(i).(j);;
	(* on prend en compte la possibilité que p appartiennent à la cellule en question *)
		
		(* ~~~~~ Fonctions de génération ~~~~~ *)
let rec genere_coordonnees () = (* génère des coordonnées se situant dans le couloir *)
	let x = Random.float (800. -. 2.*.csteRayon) in
	let y = Random.float (800. -. 2.*.csteRayon) in 
		if dans_le_couloir (x+.csteRayon) (y+.csteRayon) then (x, y)
		else genere_coordonnees ();;

(* à modifier dans le futur : 
pour l'instant, la fonction renvoie le chemin constitué du sommet le plus proche *)
let genere_chemin x y = 
	let iMin = ref 0 in 
	let xS, yS = coordonneesSommets.(0) in
	let dMin = ref (distance x y xS yS) in
	for i = 1 to Array.length coordonneesSommets - 1 do
		let xS, yS = coordonneesSommets.(i) in
		if distance x y xS yS < !dMin then
			begin 
			iMin := i;
			dMin := distance x y xS yS;
			end
	done;
	[!iMin];;
	
let genere_vitesse () = (Random.float 4.) +. 1.;;

let genere_personne () = (* génère une personne *)
	let x, y = genere_coordonnees () in 
	let c = genere_chemin x y in 
	let v = genere_vitesse () in 
	{x = x; y = y; v = v; chemin = c; tauxPanique = 0.};;

(* HELP *)
let rec ajoute_personne etage = 
	let p = genere_personne () in 
	let (i, j) = coordonnees p.x p.y in 
	if (*collision_dans_cellule i j etage p *) true then ajoute_personne etage
	else etage.(i).(j) <- p::etage.(i).(j);;	
	
let genere_etage nombrePersonnes = (* on divise la map de 800x800 en cellules de taille 50*50 *)
	let etage = Array.make_matrix n n [] in 
	for i = 0 to nombrePersonnes-1 do
		ajoute_personne etage;
	done; 
	etage;;

		(* ~~~~~ Fonctions d'affichage ~~~~~ *)
let affiche_personne p = (* affiche une personne*)
	begin
	set_color rouge;
	fill_circle (int_of_float(p.x)) (int_of_float(p.y)) (int_of_float csteRayon);
	end;;

let rec affiche_personnes l = (* affiche une liste de personne *)
	List.iter (fun p -> affiche_personne p) l;;

let supprime_personne p = (* supprime une personne *)
	begin
	set_color blanc;
	fill_circle (int_of_float(p.x)) (int_of_float(p.y)) (int_of_float csteRayon);
	end;;

let rec supprime_personnes l = (* supprime une liste de personne *)
	List.iter (fun p -> supprime_personne p) l;;

let affiche_etage etage = (* affiche etage + emplacement des personnes*)
	begin
		initialisation_etage ();
		Array.iter (fun l -> (Array.iter (fun cellule -> affiche_personnes cellule) l)) etage
	end;; 

		(* ~~~~~ Fonctions de déplacement ~~~~~ *) 
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


(*
let nouvelle_direction_si_collision p vect etage = (* analyse les possibilités de déplacement *)
	let vx2 = ref vect.vx in
	let vy2 = ref vect.vy in
	let k = ref 0 in
	let nombreAngles = Array.length angles in
	while (let (i, j) = coordonnees (p.x +. !vx2) (p.y +. !vy2) in 
				 collision_dans_cellule i j etage p) 
				 && (!k < nombreAngles) do
		let (c, d) = rotation (angles.(!k)) vect.vx vect.vy in 
			begin
				incr k;
				vx2 := c;
				vy2 := d;
			end;
	done; 
	if !k = Array.length angles then (0., 0.)
	else (!vx2, !vy2);;

*)

let nouvelle_direction_si_collision p vect etage = 
	try 
		Array.iter (fun a -> 
		let vx, vy = rotation a vect in
		let (i, j) = coordonnees (p.x +. vx) (p.y +. vy) in 
		if not (collision_dans_cellule i j etage p) then raise (DirectionTrouvee a)) 
		angles; print_int 0; (0., 0.)
	with DirectionTrouvee(a) -> rotation a vect;;

let deplacement_sans_hasard p vect etage = (* modifie les coordonnées d'une personne selon son vecteur déplacement *)
	let vx, vy = nouvelle_direction_si_collision p vect etage in
	begin
		p.x <- p.x +. vx;
		p.y <- p.y +. vy;
	end;;

let rec deplacement_avec_hasard p vect etage = (* fonction améliorée qui prend en paramètre un facteur hasard *)
	let a = Random.float 180. in 
	let vx, vy = rotation a vect in 
	let i,j = coordonnees (p.x +. vect.vx) (p.y +. vect.vy) in
	if not (collision_dans_cellule i j etage p) then
		begin 
		p.x <- p.x +. vx;
		p.y <- p.y +. vy;
		end
	else deplacement_avec_hasard p vect etage;;

let vecteur_deplacement p = (* renvoie le vecteur déplacement d'une personne pondéré par son taux panique *)
	let (xSommet, ySommet) = coordonneesSommets.(List.hd p.chemin) in 
	let v = normaliser {vx = xSommet -. p.x; vy = ySommet -. p.y} in 
		{vx = v.vx*.p.v; vy = v.vy*.p.v};; (* pondération à modifier selon le résultat*)

(*
let rec pop liste element = match liste with 
|[] -> failwith "Liste vide"
|t::q -> if t = element then q
				 else t::(pop q element);;


let applique_deplacement p etage =
	let sommetARejoindre = List.hd p.chemin in 
		let (xSommet, ySommet) = coordonneesSommets.(sommetARejoindre) in
		let tirage = Random.float 1. in 
			
			if distance p.x p.y xSommet ySommet >= csteRayon then
				if tirage < p.tauxPanique 
					then deplacement_avec_hasard p (vecteur_deplacement p sommetARejoindre) etage 
				else deplacement_sans_hasard p (vecteur_deplacement p sommetARejoindre) etage
			else (* cas où la personne est à côté de la sortie *)
				let (i, j) = coordonnees p.x p.y in
					begin
						p.x <- xSommet;
						p.y <- ySommet;
						etage.(i).(j) <- pop etage.(i).(j) p; (* à supprimer à un moment *)
						incr nombreEvacues;
					end;;
	
let applique_deplacement_liste etage k l = 
	let rec applique_deplacement_liste_aux liste = match liste with 
	|[] -> ()
	|p::q -> 
		let (i0, j0) = coordonnees p.x p.y in 
		let sommetARejoindre = List.hd p.chemin in 
		let (xSommet, ySommet) = coordonneesSommets.(sommetARejoindre) in
		let tirage = Random.float 1. in 
			begin
			if distance p.x p.y xSommet ySommet >= csteRayon then
				if tirage < p.tauxPanique 
					then deplacement_avec_hasard p (vecteur_deplacement p sommetARejoindre) etage 
				else deplacement_sans_hasard p (vecteur_deplacement p sommetARejoindre) etage
	
			else (* cas où la personne est à côté du sommet *)
				begin
					p.x <- xSommet;
					p.y <- ySommet;
					incr nombreEvacues;
				end;

			(* on actualise la position de p*)
			let (i, j) = coordonnees p.x p.y in
			if i0 <> i || j0 <> j then
				begin
					etage.(i0).(j0) <- List.tl etage.(i0).(j0);
					etage.(i).(j) <- p::etage.(i).(j);
				end;
			applique_deplacement_liste_aux q end
		in applique_deplacement_liste_aux etage.(k).(l) 
;;



let applique_deplacement_liste etage i j =
	let rec aux l = match l with
	| [] -> l
	| p::q when List.length p.chemin = 0 -> begin incr nombreEvacues; aux q end
	| p::q -> 
		let sommetARejoindre = List.hd p.chemin in
		let xSommet, ySommet = coordonneesSommets.(sommetARejoindre) in
		let tirage = Random.float 1. in 
		begin 
			if distance p.x p.y xSommet ySommet < float_of_int m then
					begin 
					print_endline "here";
					p.x <- xSommet;
					p.y <- ySommet;
					p.chemin <- List.tl p.chemin
					end
			(* les fonctions suivantes modifient les coordonnées de p *)
			else if tirage < p.tauxPanique 
					 then deplacement_avec_hasard p (vecteur_deplacement p) etage 
				 	 else deplacement_sans_hasard p (vecteur_deplacement p) etage
		end;
		let (i0, j0) = coordonnees p.x p.y in (* potentielles nouvelles coordonnées de p *)
		if (i0 <> i) || (j0 <> j) then begin etage.(i0).(j0) <- p::etage.(i0).(j0); aux q end
		else p::(aux q);
		
		in etage.(i).(j) <- aux etage.(i).(j) ;;
	
	*)	

let applique_deplacement_liste etage i j densiteEtage =
	let rec aux l = match l with
	| [] -> l
	| p::q when List.length p.chemin = 0 -> begin incr nombreEvacues; aux q end
	| p::q -> 
		let sommetARejoindre = List.hd p.chemin in
		let xSommet, ySommet = coordonneesSommets.(sommetARejoindre) in
		let tirage = Random.float 1. in 
		let ind = ref true in
		begin 
			if distance p.x p.y xSommet ySommet < float_of_int m then
					begin 
					print_endline "here";
					p.x <- xSommet;
					p.y <- ySommet;
					p.chemin <- List.tl p.chemin;
					ind := false
					end
			
			(* les fonctions suivantes modifient les coordonnées de p *)
			else 
				begin
					if tirage > densiteEtage.(i).(j) 
					then deplacement_sans_hasard p (vecteur_deplacement p) etage
					else deplacement_avec_hasard p (vecteur_deplacement p) etage
				end;
				let (i0, j0) = coordonnees p.x p.y in (* potentielles nouvelles coordonnées de p *)
					if (i0 <> i) || (j0 <> j) then begin etage.(i0).(j0) <- p::etage.(i0).(j0); ind := false end
		end;
		if !ind then p::(aux q) else aux q
		in etage.(i).(j) <- aux etage.(i).(j) ;;
		
let applique_deplacement_etage etage densiteEtage = 
	for i = 0 to n-1 do
		for j = 0 to n-1 do
			applique_deplacement_liste etage i j densiteEtage;
		done
	done;;

	(* ~~~~~ Fonction main ~~~~~ *)

(*
let main etage = 
	let time = ref (Sys.time ()) in
	let continuer = ref true in
	let toucheAppuyee = ref false in
	let touche = ref 'a' in
	
		begin
			(* page d'accueil *)
			page_accueil ();
			while !continuer do
				toucheAppuyee := key_pressed ();
				if !toucheAppuyee then
					touche := read_key ();
					if !touche = ' ' then 
						begin
							affiche_etage etage;
							toucheAppuyee := false;
							continuer := false;
						end
			done;
			continuer := true;
			(* simulation *)
			while !continuer do
				begin
					auto_synchronize false;
					applique_deplacement_etage etage;
					while Sys.time() -. !time < 0.01 do () done; (* sleep *)
					time := Sys.time();
					if arrivee_etage etage then continuer := false;
					affiche_etage etage;
					synchronize ();
				end;
			done;
			
			(* page des résultats *)
			print_float (Sys.time());
			
		end;;
*)

	(* ~~~~~ Fonction main ~~~~~ *)
let main nombrePersonnes = 
	let continuer = ref true in
	let toucheAppuyee = ref false in
	let compteur = ref 0 in 
	let densiteEtage = Array.make_matrix n n 0. in
	let etage = genere_etage nombrePersonnes in
		begin
			(* page d'accueil *)
			page_accueil ();
			while !continuer do
				toucheAppuyee := key_pressed();
				if !toucheAppuyee then
						begin
							affiche_etage etage;
							toucheAppuyee := false;
							continuer := false
						end;
			done;
			continuer := true;
			let time = ref (Sys.time ()) in
			(* simulation *)
			while !continuer do
				begin
					auto_synchronize false;
					applique_deplacement_etage etage densiteEtage;
					incr compteur;
					actualise_densite etage densiteEtage;
					affiche_etage etage;
					if !nombreEvacues = nombrePersonnes then continuer := false;
					while (Sys.time() -. !time) < 0.1 do () done; (* sleep *)
					time := Sys.time();
					synchronize ();
				end
			done;
			(* page des résultats *)
			print_float (Sys.time());
			
		end;;

(* ne pas oublier de tout évaluer car la variable nombreEvacues est globale *)
main 150;;

