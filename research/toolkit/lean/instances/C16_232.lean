import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 232 of the cap-16 certificate: slots 237568 .. 238591 -/
theorem chk_232 : chunkCheck 16 T stdSt 237568 1024 = true := by decide +kernel

end Row16
