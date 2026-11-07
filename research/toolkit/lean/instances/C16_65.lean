import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 65 of the cap-16 certificate: slots 66560 .. 67583 -/
theorem chk_65 : chunkCheck 16 T stdSt 66560 1024 = true := by decide +kernel

end Row16
