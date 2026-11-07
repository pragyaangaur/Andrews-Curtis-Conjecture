import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 27 of the cap-16 certificate: slots 27648 .. 28671 -/
theorem chk_27 : chunkCheck 16 T stdSt 27648 1024 = true := by decide +kernel

end Row16
