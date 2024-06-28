
import java.util.Scanner;
import java.util.Vector;
import java.util.Collections;

/* java Main code-groupe taux

   lit des lignes de la forme

      rang ; boursier ;

   sur l'entrée standard et afficher l'ordre d'appel sur la sortie standard
*/

class Main {

  public static void main(String[] args) {
    int code = Integer.parseInt(args[0]);
    int taux = Integer.parseInt(args[1]);
    GroupeClassement gc = new GroupeClassement(code, taux, 0);

    Vector<VoeuClasse> voeux = new Vector<>();
    Scanner sc = new Scanner(System.in);
    sc.useDelimiter("[ ;\n]");
    while (sc.hasNext()) {
      int r = sc.nextInt();
      int b = sc.nextInt();
      VoeuClasse vc = new VoeuClasse(code, r, b == 1, false);
      voeux.add(vc);
      sc.next(); // ignore la fin de la ligne
    }
    sc.close();

    System.out.println(voeux.size() + " voeux");

    Collections.sort(voeux);
    for (VoeuClasse v: voeux)
      gc.ajouterVoeu(v);

    OrdreAppel oa = gc.calculerOrdreAppel();
    for (VoeuClasse v: oa.voeux)
      System.out.println(v.rang + ";" + (v.estBoursier() ? "1" : "0") + ";");

  }

}
