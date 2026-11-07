import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 153 of the cap-16 certificate: slots 156672 .. 157695 -/
theorem chk_153 : chunkCheck 16 T stdSt 156672 1024 = true := by decide +kernel

end Row16
