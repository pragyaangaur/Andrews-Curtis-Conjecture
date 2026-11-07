import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 109 of the cap-16 certificate: slots 111616 .. 112639 -/
theorem chk_109 : chunkCheck 16 T stdSt 111616 1024 = true := by decide +kernel

end Row16
