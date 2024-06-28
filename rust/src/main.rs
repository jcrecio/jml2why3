use std::collections::VecDeque;
extern crate prusti_contracts;

#[derive(Debug,PartialEq)]
struct VoeuClasse {
    rang: i32,
    est_boursier: bool,
    est_resident: bool,
    rang_appel: i32,
}

impl VoeuClasse {
    fn new(rang: i32, est_boursier: bool, est_resident: bool) -> VoeuClasse {
        VoeuClasse { rang, est_boursier, est_resident, rang_appel: 0 }
    }
}

#[pure]
fn compare(voeux_classes: Vec<VoeuClasse>, v: VoeuClasse) -> bool {
    v == voeux_classes[v.rang as usize - 1]
}

#[requires="forall i: usize :: (0 <= i && i < voeux_classes.len()) ==> voeux_classes[i].rang == (i+1) as i32"]
#[requires="0 <= taux_min_boursiers_pourcents && taux_min_boursiers_pourcents <= 100"]
#[requires="0 <= taux_min_residents_pourcents && taux_min_residents_pourcents <= 100"]
#[ensures="forall i: usize :: (0 <= i && i < result.len()) ==> result[i].rang == (i+1) as i32"]
#[ensures="after_expiry<result>(voeux_classes.len() == before_expiry(result).len())"]
#[ensures="after_expiry<result>(forall i: usize :: (0 <= i && i < voeux_classes.len()) ==>
    before_expiry(result)[i] == voeux_classes[before_expiry(result)[i].rang as usize - 1])"]
#[ensures="after_expiry<result>(forall i: usize :: (0 <= i && i < voeux_classes.len()) ==>
    voeux_classes[i] == before_expiry(result)[(voeux_classes[i].rang_appel-1) as usize])"]
//                   ^^ TODO How to test for physical equality?
fn groupe_classement(
    voeux_classes: Vec<VoeuClasse>,
    taux_min_boursiers_pourcents: i32,
    taux_min_residents_pourcents: i32,
) -> Vec<VoeuClasse> {
    let n = voeux_classes.len();
    let mut br: VecDeque<VoeuClasse> = VecDeque::new();
    let mut bnr: VecDeque<VoeuClasse> = VecDeque::new();
    let mut nbr: VecDeque<VoeuClasse> = VecDeque::new();
    let mut nbnr: VecDeque<VoeuClasse> = VecDeque::new();
    for v in voeux_classes {
        if v.est_boursier {
            if v.est_resident {
                br.push_back(v)
            } else {
                bnr.push_back(v)
            }
        } else {
            if v.est_resident {
                nbr.push_back(v)
            } else {
                nbnr.push_back(v)
            }
        }
    }

    let nb_boursiers_total = br.len() as i32 + bnr.len() as i32;
    let nb_residents_total = br.len() as i32 + nbr.len() as i32;

    let mut ordre_appel : Vec<VoeuClasse> = Vec::new();
    for nb_appeles in 0..n {

        let nb_appeles = nb_appeles as i32;

        let nb_boursiers_restants = br.len() as i32 + bnr.len() as i32;
        let nb_residents_restants = br.len() as i32 + nbr.len() as i32;
        let nb_boursiers_appeles = nb_boursiers_total - nb_boursiers_restants;
        let nb_residents_appeles = nb_residents_total - nb_residents_restants;

        let contrainte_taux_boursiers = 0 < nb_boursiers_restants
            && (nb_boursiers_appeles * 100 < taux_min_boursiers_pourcents * (1 + nb_appeles));
        let contrainte_taux_residents = 0 < nb_residents_restants
            && (nb_residents_appeles * 100 < taux_min_residents_pourcents * (1 + nb_appeles));

        let mut meilleur : Option<&VoeuClasse> = Option::None;
        if !br.is_empty() {
            meilleur = Some(br.front().expect("br non-empty")); // Or: meilleur = br.front();
        }
        if !nbr.is_empty() && !contrainte_taux_boursiers && meilleur.map_or(true, |m| nbr.front().expect("nbr non-empty").rang < m.rang) {
            meilleur = Some(nbr.front().expect("nbr non-empty"));
        }
        if !bnr.is_empty() && !contrainte_taux_residents && meilleur.map_or(true, |m| bnr.front().expect("bnr non-empty").rang < m.rang) {
            meilleur = Some(bnr.front().expect("bnr non-empty"));
        }
        if !nbnr.is_empty() && !contrainte_taux_boursiers && !contrainte_taux_residents && meilleur.map_or(true, |m| nbnr.front().expect("nbnr non-empty").rang < m.rang) {
            meilleur = Some(nbnr.front().expect("nbnr non-empty"));
        }
        if meilleur.is_none() {
            meilleur = Some(bnr.front().expect("bnr is non-empty"));
        }

        let meilleur = {
            let meilleur = meilleur.expect("meilleur is not none");
            if meilleur.est_boursier {
                if meilleur.est_resident {
                    br.pop_front()
                } else {
                    bnr.pop_front()
                }
            } else {
                if meilleur.est_resident {
                    nbr.pop_front()
                } else {
                    nbnr.pop_front()
                }
            }
        };
        ordre_appel.push(meilleur.expect("not none"));
    }
    for i in 0..n {
        ordre_appel[i].rang_appel = i as i32 + 1;
    }
    ordre_appel
}

fn main() {
    let mut voeux_classes = Vec::new();
    voeux_classes.push(VoeuClasse::new(1, true, true));
    voeux_classes.push(VoeuClasse::new(2, true, false));
    voeux_classes.push(VoeuClasse::new(3, false, true));
    voeux_classes.push(VoeuClasse::new(4, false, false));
    voeux_classes.push(VoeuClasse::new(5, true, true));

    println!("appel - rang - boursier - resident");
    println!();
    println!("Voeux classes");
    for i in 0..voeux_classes.len() {
        let v = &voeux_classes[i];
        println!("{} - {} - {} - {}", v.rang_appel, v.rang, v.est_boursier, v.est_resident);
    }

    let ordre_appel = groupe_classement(voeux_classes, 1, 1);

    println!();
    println!("Ordre appel");
    for i in 0..ordre_appel.len() {
        let v = &ordre_appel[i];
        println!("{} - {} - {} - {}", v.rang_appel, v.rang, v.est_boursier, v.est_resident);
    }
}
