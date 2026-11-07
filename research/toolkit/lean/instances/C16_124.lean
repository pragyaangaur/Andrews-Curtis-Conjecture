import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 124 of the cap-16 certificate: slots 126976 .. 127999 -/
theorem chk_124 : chunkCheck 16 T stdSt 126976 1024 = true := by decide +kernel

end Row16
