
import Lean.Util.Paths
import LeanSearchClient.Syntax
import ProofWidgets.Component.Basic


/-! ## Example use of string diagram widgets -/
structure WindmillTriple where
  x : Nat
  y : Nat
  z : Nat
deriving DecidableEq, Repr, Inhabited,  Lean.ToJson, Lean.FromJson

structure WindmillColors where
  square? : Option String := some "grey"
  north?: Option String := "'#a1c4fd'"
  east? : Option String := "'#fda1c4'"
  south?: Option String := "'#fddca1'"
  west? : Option String := "'#c4fda1'"
deriving DecidableEq, Repr, Inhabited,  Lean.ToJson, Lean.FromJson

structure WindmillWidgetProps where
  triple? : Option WindmillTriple := none
  colors? : Option WindmillColors := some default
  mirror : Bool := false
  deriving Lean.Server.RpcEncodable

open ProofWidgets

@[widget_module]
def WindmillWidget : Component WindmillWidgetProps where
  javascript := "
    import { InteractiveCode } from '@leanprover/infoview'
    import * as React from 'react'

    export default function(props) {
      const WindmillPattern = () => {
        const subSquareSize = 20;

        // Extract the values from props
        const z = (props.triple && props.triple.z) || 5;
        const x = (props.triple && props.triple.x) || 2;
        const y = (props.triple && props.triple.y) || 3;

        // Use colors from props
        const colors = props.colors || {};
        const squareColor = colors.square || 'lightgray';
        const northColor = colors.north || '#a1c4fd'; // Default to light blue if not provided
        const eastColor = colors.east || '#fda1c4';  // Default to light pink
        const southColor = colors.south || '#fddca1'; // Default to light orange
        const westColor = colors.west || '#c4fda1';  // Default to light green

        const squareSize = z * subSquareSize;
        const rectWidth = y * subSquareSize;
        const rectHeight = x * subSquareSize;

        // Calculate the start positions to center the square in the view
        const centerX = 200;  // Assuming the viewBox width is 400
        const centerY = 200;  // Assuming the viewBox height is 400
        const startX = centerX - (squareSize / 2);
        const startY = centerY - (squareSize / 2);

        // Create SVG for the central square and the four rectangles
        const createSquares = () => {
          const elements = [];

          // Central square
          for (let row = 0; row < z; row++) {
            for (let col = 0; col < z; col++) {
              const xPos = startX + col * subSquareSize;
              const yPos = startY + row * subSquareSize;
              elements.push(
                React.createElement('rect', {
                  x: xPos, y: yPos, width: subSquareSize, height: subSquareSize,
                  fill: squareColor, stroke: 'white', strokeWidth: 0.5
                })
              );
            }
          }

          // Four rectangles with colors from props
          const rectanglePositions = [
            { x: startX, y: startY - rectHeight, rows: x, cols: y, fill: northColor }, // Top (North)
            { x: startX + squareSize, y: startY, rows: y, cols: x, fill: eastColor },  // Right (East)
            { x: startX + squareSize - rectWidth, y: startY + squareSize, rows: x, cols: y, fill: southColor }, // Bottom (South)
            { x: startX - rectHeight, y: startY + squareSize - rectWidth, rows: y, cols: x, fill: westColor }  // Left (West)
          ];

          rectanglePositions.forEach(pos => {
            for (let row = 0; row < pos.rows; row++) {
              for (let col = 0; col < pos.cols; col++) {
                const xPos = pos.x + col * subSquareSize;
                const yPos = pos.y + row * subSquareSize;
                elements.push(
                  React.createElement('rect', {
                    x: xPos, y: yPos, width: subSquareSize, height: subSquareSize,
                    fill: pos.fill, stroke: 'white', strokeWidth: 0.5
                  })
                );
              }
            }
          });

          return elements;
        };

        // Apply mirror transformation if mirror prop is true
        const transformGroup = props.mirror
          ? React.createElement('g', { transform: 'scale(-1,1) translate(-400,0)' }, createSquares())
          : createSquares();

        return React.createElement('svg', {
          width: '100%',
          height: '100%',
          viewBox: '0 0 400 400',
          style: { display: 'block', margin: '0 auto' } // Center horizontally
        }, transformGroup);
      };

      return React.createElement('div', {
        style: {
          display: 'flex',
          justifyContent: 'center',
          alignItems: 'center',
          height: '100%',
          textAlign: 'center'
        }
      }, React.createElement(WindmillPattern));
    }"

def greyColors := ( some <| {
    square? := some "lightgrey",
    north? := some "lightgrey",
    east? := some "lightgrey",
    south? := some "lightgrey",
    west? := some "lightgrey"
  } : Option WindmillColors)

#widget WindmillWidget with { triple? := some <| {x := 2, y :=7, z := 3} : WindmillWidgetProps }

#widget WindmillWidget with ({
  triple? := some ({x := 2, y :=7, z := 3}),
  mirror := True
  }: WindmillWidgetProps)

#widget WindmillWidget with { triple? := some <| {x := 5, y := 5, z := 3} : WindmillWidgetProps }

#widget WindmillWidget with { triple? := some <| {x := 3, y := 7, z := 2} : WindmillWidgetProps }

#widget WindmillWidget with ({
  triple? := some <| {x := 3, y := 7, z := 2},
  colors? := greyColors
} : WindmillWidgetProps)
