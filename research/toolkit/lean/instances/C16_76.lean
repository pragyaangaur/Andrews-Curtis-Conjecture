import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 76 of the cap-16 certificate: slots 77824 .. 78847 -/
theorem chk_76 : chunkCheck 16 T stdSt 77824 1024 = true := by decide +kernel

end Row16
