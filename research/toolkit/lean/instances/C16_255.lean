import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 255 of the cap-16 certificate: slots 261120 .. 262143 -/
theorem chk_255 : chunkCheck 16 T stdSt 261120 1024 = true := by decide +kernel

end Row16
