import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 26 of the cap-16 certificate: slots 26624 .. 27647 -/
theorem chk_26 : chunkCheck 16 T stdSt 26624 1024 = true := by decide +kernel

end Row16
