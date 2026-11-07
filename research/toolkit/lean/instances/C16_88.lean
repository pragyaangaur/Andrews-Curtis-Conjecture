import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 88 of the cap-16 certificate: slots 90112 .. 91135 -/
theorem chk_88 : chunkCheck 16 T stdSt 90112 1024 = true := by decide +kernel

end Row16
