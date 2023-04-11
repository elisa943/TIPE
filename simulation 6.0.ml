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
type personne = {mutable x:float; mutable y:float; mutable v:float; mutable chemin:int list};;

(* Variables Globales *)
let csteRayon = 8.;;
let nombreEvacues = ref 0;;
let nombreSorties = 3;;
let n = 800/50;; (* nombre de cellules par ligne ou colonne *)
let m = 50;; (* taille de la cellule *)
let epsilon = 1e-10;;
let coordonneesSommets = 
[| (50., 750.); (400., 750.); (750., 750.); (50., 50.); (400., 50.); (750., 50.) |];;
			
			(* ~~~~~ Structure de graphe ~~~~~ *)
(* 
- Liste d'arêtes
- Liste d'adjacence à privilégier pour Dijsktra
- Matrice d'adjacence
*)

let listeAdj = [| [1; 3]; [0; 4; 2]; [1; 5]; [0; 4]; [1; 3; 5]; [2; 4] |];;

			(* ~~~~~ Implémentation de la file de priorité ~~~~~ *)

type element = {sommet: int; priorite: float};;
type file_prio = element list;;

(* renvoie true si il y a changement dans la file *)
let file_prio_ajoute fp element = 
	if !fp = [] then begin fp := [element]; false end 
	else if element.priorite >= (List.hd !fp).priorite 
		then begin fp := element::!fp; false end
	else let rec aux f = match f with
	| [] -> List.rev (element::f)
	| t::q -> if element.priorite >= t.priorite then element::f
					else t::(aux q)
	in fp := aux !fp; true;; 

let file_prio_extrait fp = 
	let t = List.hd !fp in 
	fp := List.tl !fp; t;;
	
let file_prio_extrait_min fp = 
	let listeInverse = List.rev !fp in 
	let t = List.hd listeInverse in 
	fp := List.rev (List.tl listeInverse); t;;

let file_prio_vide fp = List.length fp = 0;;


let f = ref [];;
file_prio_ajoute f {sommet = 2; priorite = 5.};;
file_prio_ajoute f {sommet = 2; priorite = 10.};;
file_prio_ajoute f {sommet = 2; priorite = 88.};;
file_prio_ajoute f {sommet = 2; priorite = 550.};;
!f;;

file_prio_extrait_min f;;
!f;;

			(* ~~~~~ Algorithme de Dijkstra ~~~~~ *)
let listAdj_distances listeAdj = 
Array.mapi (fun i l -> let i0, j0 = coordonneesSommets.(i) in
	List.map (fun s -> let iS, jS = coordonneesSommets.(s) in (s,distance i0 j0 iS jS)) l) 
	listeAdj;;

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

let dijkstra listeAdj depart arrivee =
	let n = Array.length listeAdj in 
	let distancesAuxSommets = listAdj_distances listeAdj in
	let predecesseur = Array.make n (-1) in
	let visite = Array.make n false in
	let fp = file_prio_ajoute [] {sommet = depart; priorite = 0} in
		for i = 0 to n-1 do
			if i <> depart then file_prio_ajoute fp {sommet = i; priorite = min_int}
		done;
		while not visite.(arrivee) do
			let sommet = file_prio_extrait fp in
				visite.(sommet) <- true;
				if sommet <> arrivee then 
					List.iter (fun (s, d) -> 
					if not visite.(s) && s.priorite < distance - d then 
						begin 
							predecesseur.(s) <- sommet;
							file_prio_augmente_priorite s (distance-d) fp;
						end) List.nth sommet listeAdj
		done;
		let chemin = ref [arrivee] in 
		while predecesseur.(List.hd !chemin) <> -1 do
			chemin := predecesseur.(List.hd !chemin)::!chemin
			done;
		!chemin;;
		
		
			(* ~~~~~ Algorithme A* ~~~~~ *)
let distance x1 y1 x2 y2 = sqrt((x1 -. x2) ** 2. +. (y1 -. y2)**2.);;

(* Heuristique *)
let heuristique i j = 
	let xi, yi = coordonneesSommets.(i) in 
	let xj, yj = coordonneesSommets.(j) in 
	distance xi yi xj yj;;

(* listeAdj contient la liste d'adjacence dont les sommets sont accompagnés des distances
aux sommets connectés *)
(* a faire : remplacer le type enregistrement par un couple *)
let aStar listeAdj depart arrivee = 
	let n = Array.length listeAdj in 
	let predecesseur = Array.make n (-1) in (* retrouver le chemin *)
	let visite = Array.make n false in (* marquer les sommets déjà visités) *)
	let distance = Array.make n max_float in
	let filePrio = ref [] in
	let _ = file_prio_ajoute filePrio {sommet = depart; priorite = heuristique depart arrivee} in 
		distance.(depart) <- 0.;
		while not (file_prio_vide !filePrio) do
				let s = file_prio_extrait_min filePrio in
				visite.(s.sommet) <- true;
				if s.sommet = arrivee then 
						filePrio := []
				else 
					List.iter (fun (voisin, d) -> if not visite.(voisin) then 
						let _ = file_prio_ajoute filePrio {sommet = voisin; priorite = distance.(s.sommet) +. d +. heuristique voisin arrivee}
						in begin
							predecesseur.(voisin) <- s.sommet; 
							distance.(voisin) <- distance.(s.sommet) +. d;
							end) 
					listeAdj.(s.sommet)
		done;
		let chemin = ref [arrivee] in 
		let sommet = ref arrivee in
		while !sommet <> depart do
			sommet := predecesseur.(!sommet);
			chemin := !sommet::!chemin;
		done; !chemin;;	
		
let listeAdj = [| [1; 3]; [0; 4; 2]; [1; 5]; [0; 4]; [1; 3; 5]; [2; 4] |];;
let listeAdj = [|[(1, 350.); (3, 700.)]; 
					[(0, 350.); (4, 700.); (2, 350.)]; 
					[(1, 350.); (5, 700.)]; 
					[(0, 700.); (4, 350.)]; 
					[(1, 700.); (3, 350.); (5, 350.)]; 
					[(2, 700.); (4, 350.)]|];;

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

let normaliser v = 
	let n = norme v in 
	{vx = v.vx/.n; vy = v.vy/.n};;

let abs x = if x < 0. then -.x else x;;

let radian_of_degre deg = 
	(deg *. Float.pi) /. 180.;;

let rotation theta vect = (* theta en degré *)
	let x = vect.vx in
	let y = vect.vy in 
	let a = radian_of_degre theta in 
	let x' = (x *. cos a -. y *. sin a) in
	let y' = (x *. sin a +. y *. cos a) in 
	if abs x' < epsilon then 
		if abs y' < epsilon then (0., 0.)
		else (0., y')
	else 
		if abs y' < epsilon then (x', 0.)
		else (x', y');;

(*
let projection vx vy axe = match axe with 
| "abs" -> (vx, 0.)
| "ord" -> (0., vy)
| _ -> raise Stop;;
*) 

let derivee f x y var = 
	if var = 0 then ((f (x+.epsilon) y) -. (f x y))/.epsilon
	else ((f x (y+.epsilon)) -. (f x y))/.epsilon;;

let gradient f x y = 
	(derivee f x y 0, derivee f x y 1);;

let coordonnees x y = (* convertit les coordonnées (x, y) en coordonnées du tableau de l'étage *)
	let x = int_of_float x
	and y = int_of_float y in 
	((x - (x mod m))/m, (y - (y mod m))/m);;

(* flag *)	
let densite etage i j = 
	let nombrePersonnesCellule = List.length etage.(i).(j) in 
	(float_of_int nombrePersonnesCellule)/.(float_of_int (m*m));;

let actualise_densite etage densiteEtage = 
	for i = 0 to n-1 do
		for j = 0 to n-1 do
			 densiteEtage.(i).(j) <- densite etage i j
		done
	done;;

(* fonction spécifique à la map *)	
let calcul_densite_aretes densiteEtage = 
	let d = Array.make 7 0. in 
	for i = 2 to 6 do
		for j = 14 to 15 do
			d.(0) <- d.(0) +. densiteEtage.(i).(j)
		done;
		for j = 0 to 1 do
			d.(5) <- d.(5) +. densiteEtage.(i).(j)
		done
	done;
	for i = 9 to 13 do
		for j = 14 to 15 do
			d.(1) <- d.(1) +. densiteEtage.(i).(j)
		done;
		for j = 0 to 1 do
			d.(6) <- d.(6) +. densiteEtage.(i).(j)
		done
	done;
	for k = 0 to 2 do
		for i = 7*k to 7*k+1 do
			for j = 2 to 13 do
				d.(2) <- d.(2) +. densiteEtage.(i).(j)
			done
		done
	done;d;;
	
	(* A REPRENDRE *)
let calcul_densite_arete densiteEtage = 
	let d = Array.make 7 0. in 
	for i = 0 to 6 do
		d.(i) <- List.map  
	done;

let nouvelle_densite_graphe listeAdj densiteEtage = 
	let d = calcul_densite_arete densiteEtage in 
	Array.mapi (fun l i ->  
		List.map (fun j -> match ) 
			l) 
	listeAdj 	
;;

		(* ~~~~~ Fonctions de vérification ~~~~~ *)
let dans_le_couloir x y = 
	not (((100. <= x && x <= 350.) || (450. <= x && x <= 700.))
	&& (100. <= y && y <= 700.));;

let arrivee_etage etage = Array.for_all (fun l -> Array.for_all (fun cellule -> List.length cellule = 0) l) etage;;

		(* ~~~~~ Fonction de collision ~~~~~  *)
let collision x1 y1 x2 y2 = (* collision entre deux personnes *)
	(distance x1 y1 x2 y2) < 2.*.csteRayon;;

let collision_dans_cellule i j etage p x y = (* collision entre une personne et une liste de personnes *)
	List.exists (fun voisin -> p <> voisin && collision x y voisin.x voisin.y) etage.(i).(j);;
	(* on prend en compte la possibilité que p appartiennent à la cellule en question *)

		(* ~~~~~ Fonctions de génération ~~~~~ *)
let rec genere_coordonnees () = (* génère des coordonnées se situant dans le couloir *)
	let x = Random.float (800. -. 2.*.csteRayon) in
	let y = Random.float (800. -. 2.*.csteRayon) in 
		if dans_le_couloir (x+.csteRayon) (y+.csteRayon) then (x, y)
		else genere_coordonnees ();;

(* idéalement, densiteAretes devrait être de la forme d'une matrice d'adjacence *) 
let genere_chemin sommetDepart sommetArrivee densiteArete algo = 
	algo sommetDepart sommetArrivee densiteArete;;
	
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
	!iMin;; 
	
	(* flag !! *)

let genere_chemin_astar x y = 
	let iMin = genere_chemin x y in 
	aStar listeAdj iMin 1;;

let genere_vitesse () = (Random.float 3.) +. 1.;; (* 4.*)

let genere_personne () = (* génère une personne *)
	let x, y = genere_coordonnees () in 
	let c = genere_chemin_astar x y in 
	let v = genere_vitesse () in 
	{x = x; y = y; v = v; chemin = c};;

let rec ajoute_personne etage = 
	let p = genere_personne () in 
	let (i, j) = coordonnees p.x p.y in 
	if collision_dans_cellule i j etage p p.x p.y then ajoute_personne etage
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

(*
let affiche_vecteur p v = 
	begin 
		set_color vert;
		moveto (int_of_float p.x) (int_of_float p.y);
		lineto (int_of_float (p.x+.v.vx)) (int_of_float (p.y+.v.vy));
	end;;
*)

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
let angles = 
	let a = Array.make 13 0. in 
	let j = ref 1 in 
	for i = 1 to 6 do
		begin
		a.(!j) <- 15. *. float_of_int i;
		a.(!j + 1) <- -. a.(!j);
		j := !j + 2;
		end;
	done; a;;
*)

let nouvelle_direction_si_collision p vect etage = (* la fonction vérifie s'il y aura une collisition, si c'est le cas elle opère une rotation adaptée *)
	try 
		Array.iter (fun a -> 
		let vx, vy = rotation a vect in
		let (i, j) = coordonnees (p.x +. vx) (p.y +. vy) in 
		if not (collision_dans_cellule i j etage p (p.x +. vx) (p.y +. vy)) then raise (DirectionTrouvee a))
		angles; (0., 0.)
	with DirectionTrouvee(a) -> rotation a vect;;

let rec deplacement_hasard p vect etage hasard = 
	if not hasard then 
		let vx, vy = nouvelle_direction_si_collision p vect etage in
		begin
			p.x <- p.x +. vx;
			p.y <- p.y +. vy;
		end;
	else (* il faudrait gérer la notion de hasard/panique différemment *)
		let a = Random.float 180. in 
		let vx, vy = rotation a vect in 
		let i,j = coordonnees (p.x +. vect.vx) (p.y +. vect.vy) in
		if not (collision_dans_cellule i j etage p (p.x +. vect.vx) (p.y +. vect.vy)) then
			begin 
				p.x <- p.x +. vx;
				p.y <- p.y +. vy;
			end
		else deplacement_hasard p vect etage true;;


let vecteur_deplacement p = (* renvoie le vecteur déplacement d'une personne pondéré par son taux panique *)
	let (xSommet, ySommet) = coordonneesSommets.(List.hd p.chemin) in 
	let v = normaliser {vx = xSommet -. p.x; vy = ySommet -. p.y} in 
		{vx = v.vx*.p.v; vy = v.vy*.p.v};; (* pondération à modifier selon le résultat *)
(* flag *)

let vecteur_deplacement p = (* renvoie le vecteur déplacement d'une personne pondéré par son taux panique *)
	let (xSommet, ySommet) = coordonneesSommets.(List.hd p.chemin) in 
	let v = normaliser {vx = xSommet -. p.x; vy = ySommet -. p.y} in 
		{vx = v.vx*.p.v; vy = v.vy*.p.v};;


(*

let applique_deplacement_liste etage i j densiteEtage =
	let rec aux l = match l with
	| [] -> l
	| p::q when List.length p.chemin = 0 -> begin incr nombreEvacues; aux q end
	| p::q -> 
		let sommetARejoindre = List.hd p.chemin in
		let xSommet, ySommet = coordonneesSommets.(sommetARejoindre) in
		let tirage = Random.float 1. in 
		let ind = ref true in (* moche *)
		begin 
			if distance p.x p.y xSommet ySommet < csteRayon then
					begin 
					p.x <- xSommet;
					p.y <- ySommet;
					p.chemin <- List.tl p.chemin;
					ind := false
					end
			(* les fonctions suivantes modifient les coordonnées de p *)
			else
				deplacement_hasard p (vecteur_deplacement p) etage (tirage < densiteEtage.(i).(j));
				let (i0, j0) = coordonnees p.x p.y in (* potentielles nouvelles coordonnées de p *)
					if (i0 <> i) || (j0 <> j) then begin etage.(i0).(j0) <- p::etage.(i0).(j0); ind := false end
		end;
		if !ind then p::(aux q) else aux q
	in etage.(i).(j) <- aux etage.(i).(j);;

*)


exception ChangementCellule;;

let applique_deplacement_liste etage i j densiteEtage =
	let rec aux l = match l with
	| [] -> l
	| p::q -> try
		if List.length p.chemin = 0 then begin incr nombreEvacues; raise ChangementCellule end
		else
		let sommetARejoindre = List.hd p.chemin in
		let xSommet, ySommet = coordonneesSommets.(sommetARejoindre) in
		let tirage = Random.float 1. in
		begin 
			if distance p.x p.y xSommet ySommet < csteRayon && List.length p.chemin = 1 then (* proche du sommet final *)
				begin 
					p.x <- xSommet;
					p.y <- ySommet;
					p.chemin <- [];
				end	
			else if distance p.x p.y xSommet ySommet < float_of_int m (* proche du sommet à rejoindre *)
					 then p.chemin <- List.tl p.chemin
			else deplacement_hasard p (vecteur_deplacement p) etage (tirage < densiteEtage.(i).(j));
		end;
		
		begin (* si la personne a changé de cellule, il faut la supprimer de l'ancienne et l'ajouter dans la nouvelle *)
			let (i0, j0) = coordonnees p.x p.y in
			if (i0 <> i) || (j0 <> j) (* s'il y a un changement de cellule... *)
				then begin etage.(i0).(j0) <- p::etage.(i0).(j0); raise ChangementCellule end
			else p::(aux q)
		end;
		with ChangementCellule -> aux q
	in etage.(i).(j) <- aux etage.(i).(j);;


let applique_deplacement_etage etage densiteEtage = 
	for i = 0 to n-1 do
		for j = 0 to n-1 do
			applique_deplacement_liste etage i j densiteEtage;
		done
	done;;


	(* ~~~~~ Fonction main ~~~~~ *)
	(*
let main etage = 
	let nombrePersonnes = Array.length etage in
	let continuer = ref true in
	let toucheAppuyee = ref false in
	let densiteEtage = Array.make_matrix n n 0. in
	begin
		(* page d'accueil 
		page_accueil ();
		while !continuer do
			toucheAppuyee := key_pressed();
			if !toucheAppuyee then
					begin
						affiche_etage etage;
						toucheAppuyee := false;
						continuer := false
					end
		done; 
		continuer := true; *)
		let time = ref (Sys.time ()) in
		(* simulation *)
		try 
			while !continuer do
				begin
					auto_synchronize false;
					applique_deplacement_etage etage densiteEtage;
					actualise_densite etage densiteEtage;
					affiche_etage etage;
					if !nombreEvacues = nombrePersonnes then raise Stop;
					(*while Sys.time() -. !time < 0.0001 do () done; *) (* sleep *)
					time := Sys.time();
					synchronize ()
				end
			done;
		(* page des résultats *)
		with Stop -> print_endline "the end"; print_float (Sys.time());
			
	end;;
	*)
	
	(* ~~~~~ Fonction main ~~~~~ *)
let main etage densiteEtage = 
	let time = ref (Sys.time ()) in
	let nombrePersonnes = 200 in
	let attente = 0.05 in
		(* simulation *)
		try 
			while true do
				begin
					auto_synchronize false;
					applique_deplacement_etage etage densiteEtage;
					(*actualise_densite etage densiteEtage; *)
					affiche_etage etage;
					if !nombreEvacues = nombrePersonnes then raise Stop;
					while Sys.time() -. !time < attente do () done; (* sleep *)
					time := Sys.time();
					synchronize ()
				end
			done;
		(* page des résultats *)
		with Stop -> print_endline "the end : "; print_float (Sys.time());;

	
	(* ~~~~~ TESTS ~~~~~ *)
(* ne pas oublier de tout évaluer car la variable nombreEvacues est globale *)
let d = Array.make_matrix n n 0.;;
let etage = genere_etage 200;;
affiche_etage etage;;

main etage d;;
!nombreEvacues;;

(* ATTENTION 
Penser à d'abord effacer la sortie, évaluer tout ce qu'il y a avant TESTS, 
puis appeler la fonction main. 
Sinon, cela fausse le temps renvoyé par main. 
*)


(* PLAYGROUND

let xS, yS = coordonneesSommets.(3);;
List.hd etage.(0).(2);;
let p = List.hd etage.(0).(2);;
distance p.x p.y xS yS < float_of_int m;;
let v = vecteur_deplacement p;;
collision_dans_cellule 0 2 etage p (p.x +. v.vx) (p.y +. v.vy);;
nouvelle_direction_si_collision p v etage;;
let (i0, j0) = coordonnees p.x p.y;;
let (i, j) = coordonnees (p.x +. v.vx) (p.y +. v.vy);;


*)


















