type voeu = {
  rang: Z.t;
  boursier: bool;
  resident: bool;
  }

type ordre_appel_valide = {
  ordre_appel: voeu Queue.t;
  boursiers: voeu Queue.t;
  non_boursiers: voeu Queue.t;
  taux_b: Z.t;
  nb_voeux: Z.t;
  nb_b_total: Z.t;
  mutable nb_b_appeles: Z.t;
  }

let reste_b (oa: ordre_appel_valide) : bool =
  not (Queue.is_empty (oa.boursiers))

let reste_nb (oa: ordre_appel_valide) : bool =
  not (Queue.is_empty (oa.non_boursiers))

let taux_ok (taux_p: Z.t) (nb_p: Z.t) (nb_total: Z.t) : bool =
  Z.geq (Z.mul (Z.of_string "100") nb_p) (Z.mul taux_p nb_total)

let taux_b_est_contraignant_f (oa: ordre_appel_valide) : bool =
  reste_b oa && not (taux_ok (oa.taux_b) (oa.nb_b_appeles)
                       (Z.add Z.one (Z.of_int (Queue.length (oa.ordre_appel)))))

let voeu_lt (x: voeu) (y: voeu) : bool = Z.lt (x.rang) (y.rang)

let meilleur_candidat_est_b (oa: ordre_appel_valide) : bool =
  let c_nb = Queue.peek (oa.non_boursiers) in
  let c_b = Queue.peek (oa.boursiers) in
  voeu_lt c_b c_nb || (if voeu_lt c_nb c_b
                       then false
                       else assert false (* absurd *))

let creer_ordre_appel_valide (b: voeu Queue.t) (nb: voeu Queue.t) (taux: Z.t) :
  ordre_appel_valide =
  { ordre_appel = Queue.create (); boursiers = b; non_boursiers = nb;
    taux_b = taux; nb_voeux =
    Z.add (Z.of_int (Queue.length b)) (Z.of_int (Queue.length nb));
    nb_b_total = Z.of_int (Queue.length b); nb_b_appeles = Z.zero }

let choisir_boursier (oa: ordre_appel_valide) : unit =
  let v = Queue.pop (oa.boursiers) in
  oa.nb_b_appeles <- Z.add (oa.nb_b_appeles) Z.one;
  Queue.push v (oa.ordre_appel)

let choisir_non_boursier (oa: ordre_appel_valide) : unit =
  let v = Queue.pop (oa.non_boursiers) in Queue.push v (oa.ordre_appel)

let mk_ordre_appel (b: voeu Queue.t) (nb: voeu Queue.t) (taux: Z.t) :
  voeu Queue.t =
  let oa = creer_ordre_appel_valide b nb taux in
  while Z.lt (Z.of_int (Queue.length (oa.ordre_appel))) (oa.nb_voeux) do
    if taux_b_est_contraignant_f oa
    then choisir_boursier oa
    else
      begin
        if not (reste_nb oa)
        then choisir_boursier oa
        else
          begin
            if not (reste_b oa)
            then choisir_non_boursier oa
            else
              begin
                if meilleur_candidat_est_b oa
                then choisir_boursier oa
                else choisir_non_boursier oa end end end
  done;
  oa.ordre_appel

type groupe_classement = {
  voeux: voeu array;
  taux_boursiers: Z.t;
  taux_residents: Z.t;
  }

let queue_of_array : type a. (a array) ->  (a Queue.t) =
  fun a -> let q = Queue.create () in
           (let o = Z.sub (Z.of_int (Array.length a)) Z.one in
            let o1 = Z.zero in
            let rec for_loop_to i =
              if Z.leq i o
              then begin
                Queue.push (a.(Z.to_int i)) q;
                for_loop_to (Z.succ i)
              end
            in for_loop_to o1);
           q

let diviser_groupe (g: voeu Queue.t) (pred: voeu -> (bool)) :
  (voeu Queue.t) * (voeu Queue.t) =
  let g1 = Queue.create () in
  let g2 = Queue.create () in
  let n = Z.of_int (Queue.length g) in
  (let o = Z.sub n Z.one in let o1 = Z.zero in
   let rec for_loop_to1 i1 =
     if Z.leq i1 o
     then begin
       (let v = Queue.pop g in
        if pred v then Queue.push v g1 else Queue.push v g2);
       for_loop_to1 (Z.succ i1)
     end
   in for_loop_to1 o1);
  (g1, g2)

let est_boursier (p: voeu) : bool = p.boursier

let algo1 (g: groupe_classement) : voeu Queue.t =
  let voeux1 = queue_of_array (g.voeux) in
  let (boursiers1,
  non_boursiers1) =
  diviser_groupe voeux1 est_boursier in
  mk_ordre_appel boursiers1 non_boursiers1 (g.taux_boursiers)

