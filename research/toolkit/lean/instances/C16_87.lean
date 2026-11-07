import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 87 of the cap-16 certificate: slots 89088 .. 90111 -/
theorem chk_87 : chunkCheck 16 T stdSt 89088 1024 = true := by decide +kernel

end Row16
