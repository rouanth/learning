(use 'clojure.test)
(load "bitonic")

(defn lstsorted?
  "Return true if list is sorted"
  [l]
  (if (>= 1 (count l))
    true
    (let [[a b] [(first l) (first (rest l))]]
      (and (<= a b) (lstsorted? (rest l))))))

(deftest sortedtest-emp
  (is (lstsorted? [])))

(deftest sortedtest-true
  (is (lstsorted? [1 2 3 4])))

(deftest sortedtest-false
  (is (not (lstsorted? [1 3 2 4]))))

(deftest emptytest
  (is (empty? (bitonic-srt true []))))

(deftest singletest
  (is (= 1 (count (bitonic-srt true [1])))))

(deftest sortedtest
  (is (lstsorted? (bitonic-srt true [1 2 3 4 5 6 7]))))

(deftest reversetest
  (is (lstsorted? (bitonic-srt true [7 6 5 4 3 2 1]))))

(deftest huge
  (is (lstsorted? (bitonic-srt true [45 6 542 5 23 6 2 7 98 23 7 4 3]))))

(deftest really-huge
  (let [lst (take 1000 (repeatedly #(rand-int 50000)))]
    (is (lstsorted? (bitonic-srt true lst)))))

(run-tests)
