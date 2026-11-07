import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 187 of the cap-16 certificate: slots 191488 .. 192511 -/
theorem chk_187 : chunkCheck 16 T stdSt 191488 1024 = true := by decide +kernel

end Row16
