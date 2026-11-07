import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 102 of the cap-16 certificate: slots 104448 .. 105471 -/
theorem chk_102 : chunkCheck 16 T stdSt 104448 1024 = true := by decide +kernel

end Row16
