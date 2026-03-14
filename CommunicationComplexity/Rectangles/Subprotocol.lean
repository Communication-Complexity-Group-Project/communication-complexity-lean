import CommunicationComplexity.Det.Subprotocol
import CommunicationComplexity.Rectangles.Basic

namespace DetProtocol

variable {X Y α : Type*}

/-- The input pairs that reach a fixed subprotocol path form a rectangle. -/
theorem reachesPath_isRectangle {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p) :
    isRectangle {xy : X × Y | reachesPath hsp xy.1 xy.2} := by
  refine ⟨reachXPath hsp, reachYPath hsp, ?_⟩
  ext xy
  rcases xy with ⟨x, y⟩
  simp [reachesPath, Set.mem_prod]

/-- The input pairs that reach a chosen subprotocol witness form a rectangle. -/
theorem reaches_isRectangle {s p : DetProtocol X Y α} (hsp : IsSubprotocol s p) :
    isRectangle {xy : X × Y | reaches hsp xy.1 xy.2} := by
  simpa [reaches, reachX, reachY] using reachesPath_isRectangle (choosePath hsp)

end DetProtocol
