import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 78 of the cap-16 certificate: slots 79872 .. 80895 -/
theorem chk_78 : chunkCheck 16 T stdSt 79872 1024 = true := by decide +kernel

end Row16
