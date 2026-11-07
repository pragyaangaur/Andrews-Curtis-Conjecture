import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 140 of the cap-16 certificate: slots 143360 .. 144383 -/
theorem chk_140 : chunkCheck 16 T stdSt 143360 1024 = true := by decide +kernel

end Row16
