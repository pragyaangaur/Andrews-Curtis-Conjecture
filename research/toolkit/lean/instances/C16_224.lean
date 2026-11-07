import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 224 of the cap-16 certificate: slots 229376 .. 230399 -/
theorem chk_224 : chunkCheck 16 T stdSt 229376 1024 = true := by decide +kernel

end Row16
