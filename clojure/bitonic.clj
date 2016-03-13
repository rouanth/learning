(defn greatestP2ltN
  "Finds the greates power of 2 less than n"
  [n] (loop [p2 2] (if (>= p2 n) (/ p2 2) (recur (* 2 p2)))))

(defn bitonic-mrg
  "Merges bitonic sequences"
  [up coll]
  (if (= 1 (count coll))
    coll
    (let [[l1 l2] (split-at (greatestP2ltN (count coll)) coll)]
      (let [[l1' l2']
            (loop [l [] r [] l1 l1 l2 l2]
               (if (empty? l2)
                 [(concat l l1) r]
                 (let [[ln rn]
                       (let [[fl1 fl2] [(first l1) (first l2)]]
                         (if (= (< 0 (compare fl1 fl2)) up)
                           [fl2 fl1]
                           [fl1 fl2]))]
                   (recur (conj l ln) (conj r rn) (rest l1) (rest l2)))))]
        (concat (bitonic-mrg up l1') (bitonic-mrg up l2'))))))

(defn bitonic-srt
  "Bitonic sort"
  [up coll]
  (if (or (empty? coll) (= 1 (count coll)))
    coll
    (let [[l1 l2] (split-at (/ (count coll) 2) coll)]
      (bitonic-mrg up (concat (bitonic-srt (not up)  l1)
                              (bitonic-srt up        l2))))))

