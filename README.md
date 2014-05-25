cKanren
=======

This library implements `#lang kraken`, a functional-logic programming
language embedded in Racket.  It draws on inspiration from miniKanren
(see http://minikanren.org) and Racket (see http://racket-lang.org).

Please be advised that despite its miniKanren-like appearence, this
language is in no way backwards compatible. 

Installing
----------

kraken can be installed as a package within Racket 6.0 or later:

* `raco pkg install git://github.com/calvis/kraken.git`

After setup finishes, you can run the tests to make sure everything went okay:

* `raco test -p kraken`

Finally, you can view the rendered documentation by typing:

* `raco docs kraken`

License
-------

This majority of this software is released under the LGPL (see COPYING
and COPYING.LESSER).  Portions of this software are directly copied
from cKanren (see http://github.com/calvis/cKanren) and miniKanren,
and therefore are released under their MIT license.  Each file
specifies the appropriate copyright and license at the top.
