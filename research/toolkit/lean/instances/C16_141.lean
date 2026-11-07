import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 141 of the cap-16 certificate: slots 144384 .. 145407 -/
theorem chk_141 : chunkCheck 16 T stdSt 144384 1024 = true := by decide +kernel

end Row16
