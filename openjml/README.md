# Progress on verifying Parcoursup using OpenJML

## Eclipse installation

The Eclipse plugin for OpenJML is available under
[http://jmlspecs.sourceforge.net/openjml-updatesite]().

If every operation with the OpenJML plugin results in a `NullPointerException` and Eclipse
has been installed using the Oomph installer, it must instead be installed from the
`.tar.gz` (the installation directory of plugins is different when using Oomph, which
might confuse the OpenJML plugin).

## Source modifications

Applying OpenJML to the original code `GroupeClassement.java` results in a "catastrophic
error", caused by line 122, `PriorityQueue<VoeuClasse> eligibles = new
PriorityQueue<>();`. Replacing the first occurrence of `PriorityQueue` with `Queue`
resolves the issue ([Github#682](https://github.com/OpenJML/OpenJML/issues/682)).

## Initial results

Running OpenJML with standard configuration (and z3 3.4) on Hugo’s `GroupeClassement.java`
results in the 21 unproved verification conditions for method `calculerOrdreAppel()`,
detailed in file [initial-output.txt]().

## Changes on original algorithm to make it work in OpenJML

Issues and changes to original code to make OpenJML work (better)
- `enum` values not working:
  - replace enum `TypeCandidat` by two fields `estBoursier` and `estResident` 
- non-first-level mutable data
  - replace hashmap from candidate types to queues by four variables of queues
  - replace `eligibles` with `meilleur`
- `sort` not working in OpenJML:
  - make `voeuClasse` an argument, require sorted by `rang`
- simplifications
  - direct computation of `nbBoursiersTotal`/`nbResidentsTotal`,
    `nbBoursierRestants`/`nbResidentsRestants`, `nbBoursiersAppeles`/`nbResidentsAppeles`
  - replace first for-in loop by classic for-loop to have a counter
  - replace while-loop by for-loop on `nbAppeles`
- much better reasoning support for arrays than for collections (Lists, Queues)
  - use arrays instead of lists
- problems keep class invariants on queues in loop invariants
  - use arrays instead of queues (!)
    - `GroupeClassement__only_arrays` uses arrays with start and end indices as queues ("poor man's queue")
    - `GroupeClassement__array_queue` contains a custom implementation of Queues based on arrays

## OpenJML notes

- don't use `c.size()` in JML annotations but `c.content.theSize`
- put the right `loop_modifies`, there are currently no warnings when they are wrong or
  missing
