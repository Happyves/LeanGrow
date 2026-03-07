import Lean

open Lean Widget

@[widget_module]
def badWidget : Lean.Widget.Module where
  javascript := "
    import * as React from 'react';
    export default function(props) {
      return React.createElement(\"img\", {src: \"./LeanGrow/Src/Utils/Widget/gandalf.gif\"}, null)
    }
"

-- #widget badWidget

--./LeanGrow/Src/Utils/Widget/gandalf.gif


-- #html test

--<img src="path/to/your.gif" alt="Description of GIF">
