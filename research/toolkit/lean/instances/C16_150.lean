import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 150 of the cap-16 certificate: slots 153600 .. 154623 -/
theorem chk_150 : chunkCheck 16 T stdSt 153600 1024 = true := by decide +kernel

end Row16
