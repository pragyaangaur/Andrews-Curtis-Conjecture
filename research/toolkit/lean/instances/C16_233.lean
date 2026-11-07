import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 233 of the cap-16 certificate: slots 238592 .. 239615 -/
theorem chk_233 : chunkCheck 16 T stdSt 238592 1024 = true := by decide +kernel

end Row16
