import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 30 of the cap-16 certificate: slots 30720 .. 31743 -/
theorem chk_30 : chunkCheck 16 T stdSt 30720 1024 = true := by decide +kernel

end Row16
