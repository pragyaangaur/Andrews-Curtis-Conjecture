import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 179 of the cap-16 certificate: slots 183296 .. 184319 -/
theorem chk_179 : chunkCheck 16 T stdSt 183296 1024 = true := by decide +kernel

end Row16
