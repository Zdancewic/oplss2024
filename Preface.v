(** * Preface *)

(** This volume of _Software Foundations_ TODO  *)

(* ################################################################# *)
(** * Setup *)

(** For working with this material, you will need to install Coq and the ITrees
    Library.  To do this, install [opam] (OS specific) which is the [OCaml] platform
    package manager.  Add the Coq release distribution to [opam]'s databased, and then use [opam] to install [coq], [coq-itree], [coq-coinduction] as shown below:

opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq
opam install coq-itree
opam install coq-coinduction

    More detailed instructions about the Interaction Trees library can be found here:
       {https://github.com/DeepSpec/InteractionTrees/}

   Once you have installed Coq and the [coq-itree] library, you will need to compile the [.v] files by
   running [make] in the source directory.  This creates a Coq library called [RIP], which is used for
   importing the project code.

make

   This material assumes that you have proficiency in Coq up to (and including) [Imp.v] and the [Hoare.v] files from Software Foundations and Programming Language Foundations, but is self contained otherwise.

   Start (if necessary) with a refresher on [Imp.v] then try  [Monads], [Free], [ITrees],
   [ImpDenotation], [ImpEquiv], and [Hoare3].


    *)

(* ################################################################# *)
(** * Practicalities *)
(* ================================================================= *)
(** ** Recommended Citation Format *)

(** If you want to refer to this volume in your own writing, please
    do so as follows:

    @book            {Zdancewic:SF7,
    author       =   {Steve Zdancewic and
Yannick Zakowski and
Lef Ioannidis and
Jessica Shi},
    editor       =   {Benjamin C. Pierce},
    title        =   "Reasoning about Interactive Programs",
    series       =   "Software Foundations",
    volume       =   "7",
    year         =   "2024",
    publisher    =   "Electronic textbook",
    note         =   {Version 0.1, \URL{http://softwarefoundations.cis.upenn.edu} },
    }
*)

(* ################################################################# *)
(** * Thanks *)

(** Development of the _Software Foundations_ series has been
    supported, in part, by the National Science Foundation under the
    NSF Expeditions grant 1521523, _The Science of Deep
    Specification_.  Work on this volume was also supported by TODO *)

(* 2024-06-07 10:32 *)
