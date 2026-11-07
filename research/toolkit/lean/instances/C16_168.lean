import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 168 of the cap-16 certificate: slots 172032 .. 173055 -/
theorem chk_168 : chunkCheck 16 T stdSt 172032 1024 = true := by decide +kernel

end Row16
