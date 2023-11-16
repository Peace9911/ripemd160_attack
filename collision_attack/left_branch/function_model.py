import subprocess

from constrain_condition import *


class FunctionModel:
    def __init__(self, steps, bounds):
        self.__bounds_rounds = bounds
        self.__step = steps
        self.__declare = []
        self.__constraints = []
        self.__assign = []
        self.__RotateCons_left = ["-", "-", "-", "-", "-", 11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6]
        self.__OrderMessageWords_left = ["-", "-", "-", "-", "-", 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

        self.__isc = ["-", "-", "-", "-", "-", 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
        self.__isf = ["-", "-", "-", "-", "-", 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
        self.__isv = ["-", "-", "-", "-", "-", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        self.__isk = ["-", "-", "-", "-", "-", 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1]
        self.__filterBool_left = ["XOR"]

    def save_variable(self, s):
        temp = s + ": BITVECTOR(1);\n"
        if temp not in self.__declare:
            self.__declare.append(temp)
        return s

    def create_constraints(self, X, propagation_trail):
        fun = []
        for maxterm in propagation_trail:
            temp = []
            for i in range(len(maxterm)):
                if maxterm[i] == '1':
                    temp.append('(' + '~' + X[i] + ')')
                elif maxterm[i] == '0':
                    temp.append(X[i])
            fun.append('(' + "|".join(temp) + ')')
        sbox_main = 'ASSERT ' + '&'.join(fun) + '=0bin1' + ';\n'
        return sbox_main

    def right_shift(self, order, num):
        return order[num:] + order[:num]

    def addexp_model(self, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, out_var_v, out_var_d, step):

        eqn = "% ADDEXP_MODEL\n"
        eqn += "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (self.save_variable("cv6" + "_" + str(step) + "_" + str(0)),
                                                             self.save_variable("cd6" + "_" + str(step) + "_" + str(0)))
        for i in range(32):
            temp = [self.save_variable(in_var_v_0[i]), self.save_variable(in_var_d_0[i]),
                    self.save_variable(in_var_v_1[i]), self.save_variable(in_var_d_1[i]),
                    self.save_variable("cv6" + "_" + str(step) + "_" + str(i)),
                    self.save_variable("cd6" + "_" + str(step) + "_" + str(i)),
                    self.save_variable(out_var_v[i]), self.save_variable(out_var_d[i]),
                    self.save_variable("cv6" + "_" + str(step) + "_" + str(i + 1)),
                    self.save_variable("cd6" + "_" + str(step) + "_" + str(i + 1))]
            eqn += self.create_constraints(temp, addexp_model_constrain)
        self.__constraints.append(eqn)

    def boolfast_model(self, fna, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, in_var_v_2, in_var_d_2, out_var_v,
                       out_var_d):

        if fna == "ONX":
            eqn = "% boolfast_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i])]
                eqn += self.create_constraints(temp, onx_fast_contsrain)
            self.__constraints.append(eqn)
        elif fna == "XOR":
            eqn = "% boolfast_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i])]
                eqn += self.create_constraints(temp, xor_fast_contsrain)
            self.__constraints.append(eqn)

        elif fna == "IFZ":
            eqn = "% boolfast_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i])]
                eqn += self.create_constraints(temp, ifz_fast_contsrain)
            self.__constraints.append(eqn)
        elif fna == "IFX":
            eqn = "% boolfast_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i])]
                eqn += self.create_constraints(temp, ifz_fast_contsrain)
            self.__constraints.append(eqn)

        elif fna == "ONZ":
            eqn = "% boolfast_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i])]
                eqn += self.create_constraints(temp, onx_fast_contsrain)
            self.__constraints.append(eqn)

    def boolfull_model(self, fna, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, in_var_v_2, in_var_d_2, out_var_v,
                       out_var_d, in_var_0, in_var_1, in_var_2):
        print("175:boolfull_model")
        if fna == "ONX":
            eqn = "% boolfull_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(in_var_0[i]),
                        self.save_variable(in_var_1[i]),
                        self.save_variable(in_var_2[i])]
                eqn += self.create_constraints(temp, onx_full_constrain)
            self.__constraints.append(eqn)
        elif fna == "XOR":
            eqn = "% boolfull_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(in_var_0[i]),
                        self.save_variable(in_var_1[i]),
                        self.save_variable(in_var_2[i])]
                eqn += self.create_constraints(temp, xor_full_constrain)
            self.__constraints.append(eqn)

        elif fna == "IFZ":
            eqn = "% boolfull_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(in_var_0[i]),
                        self.save_variable(in_var_1[i]),
                        self.save_variable(in_var_2[i])]
                eqn += self.create_constraints(temp, ifz_full_constrain)
            self.__constraints.append(eqn)
        elif fna == "IFX":
            eqn = "% boolfull_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(in_var_1[i]),
                        self.save_variable(in_var_2[i]),
                        self.save_variable(in_var_0[i])]
                eqn += self.create_constraints(temp, ifz_full_constrain)
            self.__constraints.append(eqn)

        elif fna == "ONZ":
            eqn = "% boolfull_model " + str(fna) + "\n"
            for i in range(32):
                temp = [self.save_variable(in_var_v_2[i]),
                        self.save_variable(in_var_d_2[i]),
                        self.save_variable(in_var_v_0[i]),
                        self.save_variable(in_var_d_0[i]),
                        self.save_variable(in_var_v_1[i]),
                        self.save_variable(in_var_d_1[i]),
                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(in_var_2[i]),
                        self.save_variable(in_var_0[i]),
                        self.save_variable(in_var_1[i])]
                eqn += self.create_constraints(temp, onx_full_constrain)
            self.__constraints.append(eqn)

    def computer_q(self, in_var_v_z, in_var_d_z, in_var_v_x, in_var_d_x, in_var_z, in_var_x, in_var_q, step):
        for i in range(32):
            self.derive_cond(in_var_x[i], in_var_v_x[i], in_var_d_x[i])
            self.derive_cond(in_var_z[i], in_var_v_z[i], in_var_d_z[i])
        self.val_add_model(in_var_x, in_var_q, in_var_z, 32, step)

    def derive_cond(self, in_var_x, in_var_v_x, in_var_d_x):
        temp = [in_var_x, in_var_v_x, in_var_d_x]
        eqn = self.create_constraints(temp, derive_cond_constrain)
        self.__constraints.append(eqn)

    def expand_model(self, in_var_v, in_var_d, out_var_v, out_var_d, isK, step):

        eqn = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (self.save_variable("cv7" + "_" + str(step) + "_" + str(0)),
                                                             self.save_variable("cd7" + "_" + str(step) + "_" + str(0)))
        if isK == 1:
            for i in range(32):
                temp = [self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(in_var_v[i]),
                        self.save_variable(in_var_d[i]),
                        "cv7" + "_" + str(step) + "_" + str(i),
                        "cd7" + "_" + str(step) + "_" + str(i),
                        self.save_variable("cv7" + "_" + str(step) + "_" + str(i + 1)),
                        self.save_variable("cd7" + "_" + str(step) + "_" + str(i + 1))]
                eqn += self.create_constraints(temp, expand_model_contsrain_2)
            self.__constraints.append(eqn)
        else:
            for i in range(32):
                temp = [self.save_variable(in_var_v[i]),
                        self.save_variable(in_var_d[i]),
                        self.save_variable("cv7" + "_" + str(step) + "_" + str(i)),
                        self.save_variable("cd7" + "_" + str(step) + "_" + str(i)),

                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable("cv7" + "_" + str(step) + "_" + str(i + 1)),
                        self.save_variable("cd7" + "_" + str(step) + "_" + str(i + 1))]
                eqn += self.create_constraints(temp, expand_model_contsrain_1)
            self.__constraints.append(eqn)

    def modadd_model(self, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, in_var_c_v, in_var_c_d, out_var_v,
                     out_var_d):

        eqn = ""
        for i in range(32):
            temp = [self.save_variable(in_var_v_0[i]),
                    self.save_variable(in_var_d_0[i]),
                    self.save_variable(in_var_v_1[i]),
                    self.save_variable(in_var_d_1[i]),
                    self.save_variable(in_var_c_v[i]),
                    self.save_variable(in_var_c_d[i]),
                    self.save_variable(out_var_v[i]),
                    self.save_variable(out_var_d[i]),
                    self.save_variable(in_var_c_v[i + 1]),
                    self.save_variable(in_var_c_d[i + 1])]
            eqn += self.create_constraints(temp, modadd_model_constrain)
        self.__constraints.append(eqn)

    def rotate_model(self, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, out_var_v_0, out_var_d_0, out_var_v_1,
                     out_var_d_1, c_var_v_0, c_var_d_0):

        temp = [self.save_variable(in_var_v_0),
                self.save_variable(in_var_d_0),
                self.save_variable(in_var_v_1),
                self.save_variable(in_var_d_1),
                self.save_variable(out_var_v_0),
                self.save_variable(out_var_d_0),
                self.save_variable(out_var_v_1),
                self.save_variable(out_var_d_1),
                self.save_variable(c_var_v_0),
                self.save_variable(c_var_d_0)]
        eqn = self.create_constraints(temp, rotate_model_constrain)
        self.__constraints.append(eqn)

    def signed_q_model(self, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, in_var_v_2, in_var_d_2, out_var_v,
                       out_var_d, s):
        eqn = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (in_var_v_2[0], in_var_d_2[0])

        temp = [self.save_variable(in_var_v_0[0]),
                self.save_variable(in_var_d_0[0]),

                self.save_variable(in_var_v_1[0]),
                self.save_variable(in_var_d_1[0]),

                self.save_variable(in_var_v_2[0]),
                self.save_variable(in_var_d_2[0]),

                self.save_variable(out_var_v[0]),
                self.save_variable(out_var_d[0]),

                self.save_variable(in_var_v_2[1]),
                self.save_variable(in_var_d_2[1])]
        eqn += self.create_constraints(temp, modadd_model_constrain)
        for i in range(1, s + 1):
            temp = [self.save_variable(in_var_v_0[i]),
                    self.save_variable(in_var_d_0[i]),
                    self.save_variable("temp_v" + "_" + str(i)),
                    self.save_variable("temp_d" + "_" + str(i)),

                    self.save_variable(in_var_v_2[i]),
                    self.save_variable(in_var_d_2[i]),

                    self.save_variable(out_var_v[i]),
                    self.save_variable(out_var_d[i]),

                    self.save_variable(in_var_v_2[i + 1]),
                    self.save_variable(in_var_d_2[i + 1])]
            eqn += self.create_constraints(temp, modadd_model_constrain)
            eqn += "ASSERT temp_v" + "_" + str(i) + " = 0bin0;\n"
            eqn += "ASSERT temp_d" + "_" + str(i) + " = 0bin0;\n"
        self.__constraints.append(eqn)

    def rotate_diff_first(self, s, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, out_var_v_0, out_var_d_0, in_var_v_2,
                          in_var_d_2, isV, isK, step):

        in_var_v_b4 = []
        in_var_d_b4 = []

        for i in range(32):
            in_var_v_b4.append("bv4" + "_" + str(step) + "_" + str(i))
            in_var_d_b4.append("bd4" + "_" + str(step) + "_" + str(i))

        in_var_v_b5 = []
        in_var_d_b5 = []
        for i in range(32):
            in_var_v_b5.append("bv5" + "_" + str(step) + "_" + str(i))
            in_var_d_b5.append("bd5" + "_" + str(step) + "_" + str(i))

        in_var_v_c0 = []
        in_var_d_c0 = []
        for i in range(33):
            in_var_v_c0.append("cv0" + "_" + str(step) + "_" + str(i))
            in_var_d_c0.append("cd0" + "_" + str(step) + "_" + str(i))
        "chv" + "_" + str(step)
        "chd" + "_" + str(step)
        # ∇b4[i + s mod 32] = ∇b3[i]
        for i in range(30 - s):
            eqn = "ASSERT %s = %s;\nASSERT %s = %s;\n" % (self.save_variable(in_var_v_b4[(i + s) % 32]),
                                                          self.save_variable(in_var_v_0[i]),
                                                          self.save_variable(in_var_d_b4[(i + s) % 32]),
                                                          self.save_variable(in_var_d_0[i]))
            self.__constraints.append(eqn)
        for i in range(32 - s, 30):
            eqn = "ASSERT %s = %s;\nASSERT %s = %s;\n" % (self.save_variable(in_var_v_b4[(i + s) % 32]),
                                                          self.save_variable(in_var_v_0[i]),
                                                          self.save_variable(in_var_d_b4[(i + s) % 32]),
                                                          self.save_variable(in_var_d_0[i]))
            self.__constraints.append(eqn)

        self.rotate_model(in_var_v_0[31 - s], in_var_d_0[31 - s],
                          in_var_v_0[30 - s], in_var_d_0[30 - s],
                          in_var_v_b4[31], in_var_d_b4[31],
                          in_var_v_b4[30], in_var_d_b4[30],
                          in_var_v_c0[0], in_var_d_c0[0])

        self.rotate_model(in_var_v_0[31], in_var_d_0[31],
                          in_var_v_0[30], in_var_d_0[30],
                          in_var_v_b4[(31 + s) % 32], in_var_d_b4[(31 + s) % 32],
                          in_var_v_b4[(30 + s) % 32], in_var_d_b4[(30 + s) % 32],
                          "chv" + "_" + str(step),
                          "chd" + "_" + str(step))
        self.modadd_model(in_var_v_1, in_var_d_1, in_var_v_b4, in_var_d_b4, in_var_v_c0, in_var_d_c0,
                          in_var_v_b5, in_var_d_b5)
        self.expand_model(in_var_v_b5, in_var_d_b5, out_var_v_0, out_var_d_0, isK, step)
        if isV == 1:
            in_var_v_c1 = []
            in_var_d_c1 = []
            for i in range(33):
                in_var_v_c1.append("cv1" + "_" + str(step) + "_" + str(i))
                in_var_d_c1.append("cd1" + "_" + str(step) + "_" + str(i))
            self.signed_q_model(in_var_v_b4, in_var_d_b4, in_var_v_c0, in_var_d_c0, in_var_v_c1,
                                in_var_d_c1, in_var_v_2, in_var_d_2, s)

    def left_shift(self, order, num):
        return order[-num:] + order[:-num]

    def rotate_diff_second(self, s, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, out_var_v_0, out_var_d_0,
                           in_var_v_2, in_var_d_2, isV, isK, step):
        in_var_v_b4 = []
        in_var_d_b4 = []
        for i in range(32):
            in_var_v_b4.append("bv4" + "_" + str(step) + "_" + str(i))
            in_var_d_b4.append("bd4" + "_" + str(step) + "_" + str(i))
        self.expand_model(in_var_v_b4, in_var_d_b4, in_var_v_0, in_var_d_0, isK, step)
        self.addexp_model(in_var_v_1, in_var_d_1, self.left_shift(in_var_v_b4, s), self.left_shift(in_var_d_b4, s),
                          out_var_v_0, out_var_d_0, step)
        eqn = ""
        if isV == 1:
            for i in range(s + 1):
                eqn += "ASSERT %s = %s;\n" % (
                    self.save_variable(in_var_v_2[i]), self.save_variable(in_var_v_b4[((i - s) + 32) % 32]))
                eqn += "ASSERT %s = %s;\n" % (
                    self.save_variable(in_var_d_2[i]), self.save_variable(in_var_d_b4[((i - s) + 32) % 32]))
            self.__constraints.append(eqn)

    def val_add_model(self, a, b, v, l, step):

        eqn = "ASSERT c" + "_" + str(step) + "_" + str(0) + " = 0bin0;\n"
        for i in range(l):
            temp = [self.save_variable(a[i]),
                    self.save_variable(b[i]),
                    self.save_variable("c" + "_" + str(step) + "_" + str(i)),
                    self.save_variable(v[i]),
                    self.save_variable("c" + "_" + str(step) + "_" + str(i + 1))]
            eqn += self.create_constraints(temp, modadd_model_origin)
        self.__constraints.append(eqn)

    def val_diff_add_model(self, in_var_v_a, in_var_d_a, b, v, l, num, step):
        eqn = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (
            self.save_variable("cv" + str(num) + "_" + str(step) + "_" + str(0)),
            self.save_variable("cd" + str(num) + "_" + str(step) + "_" + str(0)))
        for i in range(l):
            temp = [self.save_variable(in_var_v_a[i]),
                    self.save_variable(in_var_d_a[i]),

                    self.save_variable(b[i]),
                    self.save_variable("cv" + str(num) + "_" + str(step) + "_" + str(i)),
                    self.save_variable("cd" + str(num) + "_" + str(step) + "_" + str(i)),

                    self.save_variable("cv" + str(num) + "_" + str(step) + "_" + str(i + 1)),
                    self.save_variable("cd" + str(num) + "_" + str(step) + "_" + str(i + 1)),

                    self.save_variable(v[i])]
            eqn += self.create_constraints(temp, val_diff_add_constrain)

        self.__constraints.append(eqn)

    def rotate_diff_filter(self, s, in_var_v_a5, in_var_d_a5, in_var_v_a1, in_var_d_a1, in_var_v_b3, in_var_d_b3,
                           in_var_v_q, in_var_d_q, in_var_a5, in_var_a1, step):

        # Claim a binary vector q of size 32
        q = []
        for i in range(32):
            q.append("q" + "_" + str(step) + "_" + str(i))
        self.computer_q(in_var_v_a5, in_var_d_a5, in_var_v_a1, in_var_d_a1, in_var_a5, in_var_a1, q, step)
        # Claim a binary vector v0 of size s + 1
        v0 = []
        for i in range(s + 1):
            v0.append("v0" + "_" + str(step) + "_" + str(i))
        self.val_diff_add_model(in_var_v_q, in_var_d_q, q, v0, s + 1, 4, step)
        # Claim a binary vector v1 of size 33 − s
        v1 = []
        for i in range(33 - s):
            v1.append("v1" + "_" + str(step) + "_" + str(i))
        self.val_diff_add_model(in_var_v_b3, in_var_d_b3, self.right_shift(q, s), v1, 33 - s, 5, step)
        eqn = "ASSERT %s = %s;\n" % (self.save_variable(v0[0]), self.save_variable(v1[32 - s]))
        eqn += "ASSERT %s = %s;\n" % (self.save_variable(v0[s]), self.save_variable(v1[0]))
        self.__constraints.append(eqn)

    def R(self, fNa, isC, isF, isV, isK, s, in_var_v_m, in_var_d_m, in_var_v_a0, in_var_d_a0, in_var_v_a1,
          in_var_d_a1, in_var_v_a2, in_var_d_a2, in_var_v_a3, in_var_d_a3, in_var_v_a4, in_var_d_a4, in_var_v_a5,
          in_var_d_a5, in_var_a4, in_var_a3, in_var_a2, in_var_a5, in_var_a1, step):
        # Claim signed difference vectors ∇b0,∇b1,∇b2,∇b3 of size 32,let a reputation b0, b1,b2,b3
        in_var_v_b = []
        in_var_d_b = []
        for i in range(4):
            temp_v = []
            temp_d = []
            for j in range(32):
                temp_v.append("bv" + str(i) + "_" + str(step) + "_" + str(j))
                temp_d.append("bd" + str(i) + "_" + str(step) + "_" + str(j))
            in_var_v_b.append(temp_v)
            in_var_d_b.append(temp_d)

        # Claim signed difference vectors ∇c2,∇c3 of size 33.
        in_var_v_c2 = []
        in_var_d_c2 = []
        in_var_v_c3 = []
        in_var_d_c3 = []
        for i in range(33):
            in_var_v_c2.append("cv2" + "_" + str(step) + "_" + str(i))
            in_var_d_c2.append("cd2" + "_" + str(step) + "_" + str(i))
            in_var_v_c3.append("cv3" + "_" + str(step) + "_" + str(i))
            in_var_d_c3.append("cd3" + "_" + str(step) + "_" + str(i))
        # Claim a signed difference vector ∇q of size s + 1.
        in_var_v_q = []
        in_var_d_q = []
        for i in range(s + 1):
            in_var_v_q.append("qv" + "_" + str(step) + "_" + str(i))
            in_var_d_q.append("qd" + "_" + str(step) + "_" + str(i))

        eqn = "% assign m to b0\n"
        for i in range(32):
            eqn += "ASSERT %s = %s;\n" % (self.save_variable(in_var_v_m[i]), self.save_variable(in_var_v_b[0][i]))
            eqn += "ASSERT %s = %s;\n" % (self.save_variable(in_var_d_m[i]), self.save_variable(in_var_d_b[0][i]))
        self.__constraints.append(eqn)
        self.boolfast_model(fNa, in_var_v_a4, in_var_d_a4, in_var_v_a3, in_var_d_a3, in_var_v_a2, in_var_d_a2,
                            in_var_v_b[1], in_var_d_b[1])
        if isC == 1:
            self.boolfull_model(fNa, in_var_v_a4, in_var_d_a4, in_var_v_a3, in_var_d_a3, in_var_v_a2,
                                in_var_d_a2, in_var_v_b[1], in_var_d_b[1], in_var_a4, in_var_a3, in_var_a2)
        # no carry for the least significant bit.
        eqn = "% no carry for the least significant bit 这部分是两个模加运算\n"
        eqn += "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (self.save_variable(in_var_v_c2[0]),
                                                             self.save_variable(in_var_d_c2[0]))
        eqn += "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (self.save_variable(in_var_v_c3[0]),
                                                             self.save_variable(in_var_d_c3[0]))
        self.__constraints.append(eqn)
        self.modadd_model(in_var_v_b[0], in_var_d_b[0], in_var_v_b[1], in_var_d_b[1], in_var_v_c2, in_var_d_c2,
                          in_var_v_b[2], in_var_d_b[2])
        self.modadd_model(in_var_v_b[2], in_var_d_b[2], in_var_v_a0, in_var_d_a0, in_var_v_c3, in_var_d_c3,
                          in_var_v_b[3], in_var_d_b[3])
        if isF == 1:
            self.rotate_diff_first(s, in_var_v_b[3], in_var_d_b[3], in_var_v_a1, in_var_d_a1, in_var_v_a5,
                                   in_var_d_a5, in_var_v_q, in_var_d_q, isV, isK, step)
        else:
            self.rotate_diff_second(s, in_var_v_b[3], in_var_d_b[3], in_var_v_a1, in_var_d_a1, in_var_v_a5,
                                    in_var_d_a5, in_var_v_q, in_var_d_q, isV, isK, step)
        if isV == 1:
            self.rotate_diff_filter(s, in_var_v_a5, in_var_d_a5, in_var_v_a1, in_var_d_a1, in_var_v_b[3],
                                    in_var_d_b[3], in_var_v_q, in_var_d_q, in_var_a5, in_var_a1, step)

    """检查赋值是否重复"""

    def check_assign(self, s):
        if s not in self.__assign:
            self.__assign.append(s)

    def assign_value(self):
        for i in range(13, 18):
            for j in range(32):
                temp = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (self.save_variable("xd_" + str(i) + "_" + str(j)),
                                                                     self.save_variable("xv_" + str(i) + "_" + str(j)))
                self.check_assign(temp)
        for i in range(0, 5):
            for j in range(32):
                temp = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (self.save_variable("xd_" + str(i) + "_" + str(j)),
                                                                     self.save_variable("xv_" + str(i) + "_" + str(j)))
                self.check_assign(temp)

        for i in range(16):
            if i == 0:
                for j in range(32):
                    if j == 17 :
                        temp = "ASSERT %s = 0bin1;\nASSERT %s = 0bin1;\n" % (
                            self.save_variable("md_" + str(i) + "_" + str(j)),
                            self.save_variable("mv_" + str(i) + "_" + str(j)))
                        self.check_assign(temp)
                    else:
                        temp = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (
                            self.save_variable("md_" + str(i) + "_" + str(j)),
                            self.save_variable("mv_" + str(i) + "_" + str(j)))
                        self.check_assign(temp)
            elif i == 2:
                for j in range(32):
                    if j == 21 :
                        temp = "ASSERT %s = 0bin1;\nASSERT %s = 0bin1;\n" % (
                            self.save_variable("md_" + str(i) + "_" + str(j)),
                            self.save_variable("mv_" + str(i) + "_" + str(j)))
                        self.check_assign(temp)
                    else:
                        temp = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (
                            self.save_variable("md_" + str(i) + "_" + str(j)),
                            self.save_variable("mv_" + str(i) + "_" + str(j)))
                        self.check_assign(temp)
            elif i == 11:
                for j in range(32):
                    if j == 7 :
                        temp = "ASSERT %s = 0bin1;\nASSERT %s = 0bin0;\n" % (
                            self.save_variable("md_" + str(i) + "_" + str(j)),
                            self.save_variable("mv_" + str(i) + "_" + str(j)))
                        self.check_assign(temp)
                    else:
                        temp = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (
                            self.save_variable("md_" + str(i) + "_" + str(j)),
                            self.save_variable("mv_" + str(i) + "_" + str(j)))
                        self.check_assign(temp)
            elif i == 12:
                for j in range(32):
                    if j == 15 :
                        temp = "ASSERT %s = 0bin1;\nASSERT %s = 0bin0;\n" % (
                            self.save_variable("md_" + str(i) + "_" + str(j)),
                            self.save_variable("mv_" + str(i) + "_" + str(j)))
                        self.check_assign(temp)
                    else:
                        temp = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (
                            self.save_variable("md_" + str(i) + "_" + str(j)),
                            self.save_variable("mv_" + str(i) + "_" + str(j)))
                        self.check_assign(temp)
            else:
                for j in range(32):
                    temp = "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (
                        self.save_variable("md_" + str(i) + "_" + str(j)),
                        self.save_variable("mv_" + str(i) + "_" + str(j)))
                    self.check_assign(temp)

    def Object(self, object_value):
        obj = "ASSERT BVPLUS(10,"
        for i in range(5, 13):
            for j in range(32):
                if i == 12 and j == 31:
                    obj += "0bin000000000@xd_%s_%s) = 0bin" % (i, j) + bin(object_value)[2:].zfill(10) + ";\n"
                else:
                    obj += "0bin000000000@xd_%s_%s" % (i, j) + ", "

        return obj

    def main(self):
        in_var_v_a = []
        in_var_d_a = []
        in_var_v_m = []
        in_var_d_m = []
        in_var_a = []
        for step in range(0, self.__bounds_rounds):
            temp_v_a = []
            temp_d_a = []
            temp_a = []
            for i in range(32):
                temp_v_a.append("xv_" + str(step) + "_" + str(i))
                temp_d_a.append("xd_" + str(step) + "_" + str(i))
                temp_a.append("x_" + str(step) + "_" + str(i))
            in_var_v_a.append(temp_v_a)
            in_var_d_a.append(temp_d_a)

            in_var_a.append(temp_a)
        for step in range(0, self.__bounds_rounds):
            temp_v_m = []
            temp_d_m = []
            for i in range(32):
                temp_v_m.append("mv_" + str(self.__OrderMessageWords_left[step]) + "_" + str(i))
                temp_d_m.append("md_" + str(self.__OrderMessageWords_left[step]) + "_" + str(i))
            in_var_v_m.append(temp_v_m)
            in_var_d_m.append(temp_d_m)

        for i in range(self.__step, self.__bounds_rounds):
            self.R(self.__filterBool_left[(i - 5) // 16], self.__isc[i], self.__isf[i], self.__isv[i],
                   self.__isk[i],
                   self.__RotateCons_left[i],
                   in_var_v_m[i],
                   in_var_d_m[i],
                   self.left_shift(in_var_v_a[i - 5], 10),
                   self.left_shift(in_var_d_a[i - 5], 10),
                   self.left_shift(in_var_v_a[i - 4], 10),
                   self.left_shift(in_var_d_a[i - 4], 10),
                   self.left_shift(in_var_v_a[i - 3], 10),
                   self.left_shift(in_var_d_a[i - 3], 10),
                   in_var_v_a[i - 2],
                   in_var_d_a[i - 2],
                   in_var_v_a[i - 1],
                   in_var_d_a[i - 1],
                   in_var_v_a[i],
                   in_var_d_a[i],

                   in_var_a[i - 1],
                   in_var_a[i - 2],
                   self.left_shift(in_var_a[i - 3], 10),
                   in_var_a[i],
                   self.left_shift(in_var_a[i - 4], 10),
                   i)

    def solver(self):
        self.main()
        self.assign_value()
        constrain = "".join(self.__constraints)
        assign = "".join(self.__assign)
        variable = "".join(self.__declare)
        query = '\n' + 'QUERY FALSE;\nCOUNTEREXAMPLE;'

        for i in range(45, 70):
            print("差分路线中有差分的个数为:%s" % i)
            obj = self.Object(i)
            file_write = open("right_model.cvc", "w")
            file_write.write(variable)
            file_write.write(constrain)
            file_write.write(assign)
            file_write.write(obj)
            file_write.write(query)
            file_write.close()
            stp_parameters = ["stp", "right_model.cvc", "--cryptominisat", "--threads", "16"]
            R = subprocess.check_output(stp_parameters)

            if "Valid.\n" != R.decode():
                file = open("right_res_0_9_" + str(i) + ".out", "w")
                print("差分路线中有差分的个数为:%s 满足" % i)
                file.write(R.decode())
                file.close()
                break
            else:
                print("差分路线中有差分的个数为:%s 不满足" % i)


if __name__ == '__main__':
    step = 5
    bounds = 18
    FunctionModel(step, bounds).solver()
