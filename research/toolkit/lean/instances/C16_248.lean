import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 248 of the cap-16 certificate: slots 253952 .. 254975 -/
theorem chk_248 : chunkCheck 16 T stdSt 253952 1024 = true := by decide +kernel

end Row16
