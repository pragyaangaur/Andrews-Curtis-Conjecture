import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 100 of the cap-16 certificate: slots 102400 .. 103423 -/
theorem chk_100 : chunkCheck 16 T stdSt 102400 1024 = true := by decide +kernel

end Row16
