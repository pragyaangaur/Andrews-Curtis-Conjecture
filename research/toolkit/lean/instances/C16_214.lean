import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 214 of the cap-16 certificate: slots 219136 .. 220159 -/
theorem chk_214 : chunkCheck 16 T stdSt 219136 1024 = true := by decide +kernel

end Row16
